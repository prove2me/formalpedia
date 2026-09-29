-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/7e2be2ef-d284-5eef-8b93-b1e72c1ec40b
-- title:
--   Frobenius equivariance of the special-fibre dictionary for J_H(M)
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p \neq 0$, and assume $j$ (as the Laurent series `jqModC ℚ`) lies in the function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak X$ be a model `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\Lambda$ be level data and $O$ a `JHNeronObjectAtP p M H hpM A hA Λ`, with $\Lambda.\sigma_A = \operatorname{Spec} \rho$. The hypothesis `hsp` (summarised here) asserts the point-reduction compatibility of the dictionaries: for each $i \in \{0,1\}$, given two $\overline{\mathbb{Q}}$-points $y_1,y_2$ of $\mathfrak X.\mathrm{Meta}$, sections $u_1,u_2$ of the model over $\operatorname{Spec}\rho$ with image in the smooth locus extending them, their reductions $u_{\kappa,1},u_{\kappa,2}$ to the special fibre, closed points $P_1,P_2$ of the fibre curve model $\mathfrak X.\mathrm{Mfib}$ lying under those reductions through the $i$-th component map, a degree-zero divisor $Dv$ equal to $[\,y_1\,]-[\,y_2\,]$ under `pointEquivPlace`, and an admissible gluing datum $x$ for $O.\mathrm{ssFinset}$ whose first component is $[P_1]-[P_2]$ if $i=0$ and $0$ otherwise, whose second component is $[P_1]-[P_2]$ if $i=1$ and $0$ otherwise, and whose unit component is $0$, there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}$ of the class of $Dv$ equal to $s$ composed with the generic point, and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt A` equal to the glued class of $x$. Finally let $\mathrm{frob}$ be a semilinear automorphism of `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$ acting on Laurent coefficients by $c \mapsto c^p$, stabilising the node set $O.\mathrm{ssFinset}$ in the sense that it carries each pair in the set to a pair in the set, let $\varphi_\kappa : \kappa \to \kappa$ be the ring homomorphism $a \mapsto a^p$, and let $\tau$ be an endomorphism of $\operatorname{Spec}\kappa$ over `resPt A ≫ Λ.σA` whose underlying morphism is $\operatorname{Spec}\varphi_\kappa$. Then for every $\kappa$-point $y$ of $O.g$ over `resPt A ≫ Λ.σA`, the class $O.\mathrm{ptsSp}^{-1}$ of the point obtained from $y$ by precomposition with $\tau$ equals the image of $O.\mathrm{ptsSp}^{-1}(y)$ under the map `GluedPic0.glueMap` induced on the glued Picard group by $\mathrm{frob}$.
--
--   This is the Frobenius equivariance of the Deligne–Rapoport/Raynaud description of the special fibre of the Néron model of $J_H(M)$ at a prime exactly dividing the level: the identification of the $\kappa$-points of the special fibre with the Picard group of the glued curve intertwines the $p$-power Frobenius twist of points with the semilinear Frobenius action on divisor classes. It is used in the computation of the action of $U_p$ and the diamond operators on the special fibre and in the identification of the Frobenius permutation of the supersingular nodes, which feed into the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (hsp : (∀ (i : Fin 2)
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
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x))
    (frob : SemilinearAut (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hfrob : ∀ (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) (n : ℤ),
      ((frob • x : ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM))) :
          LaurentSeries (ResidueField ↥A)).coeff n =
        ((x : LaurentSeries (ResidueField ↥A)).coeff n) ^ p)
    (hstab : SemilinearAut.IsNodeStable O.ssFinset frob)
    (φκ : ResidueField ↥A →+* ResidueField ↥A) (hφκ : ∀ a : ResidueField ↥A, φκ a = a ^ p)
    (τ : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA))
    (hτ : τ.1 = Spec.map (CommRingCat.ofHom φκ))
    (y : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 y) =
      GluedPic0.glueMap O.ssFinset frob hstab (O.ptsSp.symm y) := by sorry
