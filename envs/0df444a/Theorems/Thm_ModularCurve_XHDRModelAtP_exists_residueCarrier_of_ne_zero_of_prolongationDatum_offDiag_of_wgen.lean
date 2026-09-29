-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
-- name    : ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/cc954a8e-1c2c-5179-b166-e402baa3c64c
-- title:
--   Existence of a residue carrier for a prescribed jump varpi
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$; assume $j$, as a Laurent series, lies in the level-$\top$ $q$-expansion function field, and let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, the bundled integral model of $X_H(M)$ over $R p$ together with a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field $F_M =$ `xHFunctionFieldBar M H`. Let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $p$ in its non-units, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R p \to A$ be compatible with the structure map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ reducing to $p$, and let $\delta$ be the map on places of $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` given by the action, through `SemilinearAut.ofAlgAut`, of the diamond automorphism `diamondActionModL` attached to a $\Gamma_0(M/p)$-lift of $pb$. Let $SS$ be a finset of pairs of places of $\bar F$ whose members are exactly the pairs $s$ with $s.2$ supersingular and $s.1$ the mod-$p$ Frobenius place of $s.2$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb{Q}}$-algebra map with $\alpha$ and $\theta \circ \alpha$ integral, $F_{M/p}$ being the function field at level $M/p$ with the image subgroup `infSubgroup`, and let $Psp$ be a place specialisation datum and $Rpd$ a prolongation datum for $Psp$ and $\theta$, so that $Rpd$ consists of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in $\bar F$, with $f \in R_2$ precisely when $\theta f \in R_1$ and matching residues. Assume: $\alpha$ is the identity on $q$-expansions and $\theta \circ \alpha$ acts on them as `qExpand` by $p$; $\theta$ commutes with the arithmetic Galois action; the Atkin–Lehner compatibility `hwgen`, which says that two $\overline{\mathbb{Q}}$-points of `Meta` related by $\mathfrak{X}.w$ have places related by $\theta$; the type dichotomy `TypeDichotomy`, the model laws `IsModel`, the fixed-place order law, and the regularity and node-value laws for $SS$; and two families `hcompat`, `hcompat'` identifying the places of the fibre model attached to closed points over the residue field with `reduceFst`, `reduceSnd` and their Frobenius twists (summarised here). Then for every $\varpi \neq 0$ in $\overline{\mathbb{Q}}$ there is a nonzero $h \in F_M$ such that $h$ lies in the valuation ring of $R_1$ with nonzero $R_1$-residue, $\varpi^{-1} h$ lies in the valuation ring of $R_2$ with nonzero $R_2$-residue, and every place $V$ of $F_M$ over $\overline{\mathbb{Q}}$ with $\operatorname{ord}_V h \neq 0$ that is neither `IsStrictFst` nor `IsStrictSnd` satisfies $\operatorname{red}_1(V) = s.1$ for some $s \in SS$.
--
--   This is the realisation step for the jump between the two Gauss valuations attached to the two components of the special fibre at a prime exactly dividing the level: any prescribed ratio $\varpi$ of the two residues is achieved by a single function whose remaining zeros and poles are confined to the supersingular gluing pairs. It feeds the Raynaud-style computation of divisor classes on the semistable model, being used in [`ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.isGoodClass_of_forall_dvd_ord_residue_of_annulus_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ϖ : AlgebraicClosure ℚ) (hϖ : ϖ ≠ 0) :
    ∃ h : ↥(xHFunctionFieldBar M H), h ≠ 0 ∧
      (∃ h₁ : h ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨h, h₁⟩ ≠ 0) ∧
      (∃ h₂ : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ϖ)⁻¹ * h ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h₂⟩ ≠ 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord h ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by sorry
