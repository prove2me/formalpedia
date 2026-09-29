-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
-- name    : ModularCurve.JHNeronObjectAtP.levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/318ecbe6-80d4-5901-9be1-d87c3474edff
-- title:
--   Frobenius equivariance of the special-fibre dictionary Λ.ptsSp
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and assume $j$, as a Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$; let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$; let $\Lambda$ be level data (a structure morphism $\sigma_A : \operatorname{Spec} A \to$ `base p`, a scheme $\Lambda.X$ with morphism $\Lambda.f$ carrying a relative group law, a parametrisation of $J_{H'}(M/p)$-points by sections over the generic point, and a bijection $\Lambda.\mathrm{ptsSp}$ from $\operatorname{Pic}^0$ of the level-$\Gamma_N(p,M,H)$ $q$-expansion function field over $\kappa$ onto the sections of $\Lambda.f$ over `resPt A ≫ Λ.σA`), and let $O$ be a `JHNeronObjectAtP` over $\Lambda$. Let $\rho : R_p \to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ the structure map $R_p \to \overline{\mathbb{Q}}$, with $\Lambda.\sigma_A = \operatorname{Spec}(\rho)$. Assume the point-reduction dictionary `hsp` for $O$: for each index $i \in \{0,1\}$, each pair of geometric points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base together with lifts $u_1, u_2$ over $\operatorname{Spec}(\rho)$ compatible with $\mathfrak{X}.\mathrm{eeta}$ and landing in the smooth locus, residue-field points $u_{\kappa,1}, u_{\kappa,2}$ of the fibre reducing them, closed points $P_1, P_2$ of the fibre curve model matching those reductions, a degree-zero divisor $Dv$ equal to the difference of the places of $y_1$ and $y_2$, and an admissible glued datum $x$ whose first (resp. second) component is the difference of the places of $P_1$ and $P_2$ when $i = 0$ (resp. $i = 1$) and $0$ otherwise, with third component $0$, there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of } Dv))_1 = \mathrm{barPt}(A) \circ s_1$ and $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ to the residue-field point equal to the glued class of $x$ (these hypotheses are summarised here). Let $F$ be an additive endomorphism of $\operatorname{Pic}^0$ of that function field over $\kappa$ agreeing pointwise with `qExpFrobeniusPushforwardModL`, and let $\tau_F$ be an endomorphism of `resPt A ≫ Λ.σA` over itself whose underlying morphism is $\operatorname{Spec}$ of the $p$-power Frobenius of $\kappa$. Then for every class $z$ one has $\Lambda.\mathrm{ptsSp}(F z) = \tau_F$ followed by $\Lambda.\mathrm{ptsSp}(z)$.
--
--   This is the compatibility between the Frobenius push-forward on divisor classes of the mod-$p$ modular function field and the absolute Frobenius twist of special-fibre points, expressed through the dictionary $\Lambda.\mathrm{ptsSp}$ of the level-$\Gamma_{H'}(M/p)$ object. It feeds the analysis of the $U_p$ operator on the special fibre at $p \parallel M$, in particular the descent statement with the diamond operators and the identification of the relevant composite with a Verschiebung.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.JHNeronObjectAtP.levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (F : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)

    (τF : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA))
    (hτF : τF.1 = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p))) :
    ∀ z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (F z) = GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 (Λ.ptsSp z) := by sorry
