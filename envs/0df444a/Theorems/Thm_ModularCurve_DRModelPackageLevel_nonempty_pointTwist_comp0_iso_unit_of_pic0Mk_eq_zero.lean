-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero
-- name    : ModularCurve.DRModelPackageLevel.nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/32014d99-59de-5910-ac02-0a80ee255f33
-- title:
--   Vanishing divisor class trivialises a point twist on the special fibre
-- statement:
--   Fix natural numbers $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package `𝔓 : DRModelPackageLevel N₀ p hpN₀`, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$; let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of $R_p$, so that the residue field $\kappa_A$ has characteristic $p$ and becomes an $R_p$-algebra through $\rho$ followed by reduction. Assume the base change $c$ of $\mathrm{toBase0}\ N_0\ p : X_0(N_0) \to \operatorname{Spec} R_p$ along $\operatorname{Spec}\kappa_A \to \operatorname{Spec} R_p$ is proper, and let $\varepsilon_0$ be a section of $\mathrm{toBase0}$ over $\operatorname{Spec} R_p$. Given $n$, labels $c_i \in \{0,1\}$, sections $z_i$ of $c$ (that is, $\kappa_A$-points of the fibre $\mathrm{pullback}$), places $w_i$ of $\mathrm{modularFunctionFieldC}\ \kappa_A\ N_0$ over $\kappa_A$ such that for each $i$ the image of the closed point of $z_i$ under the inverse of the package isomorphism `𝔓.efib` is a closed point of the curve model `𝔓.Mfib` whose associated place is $w_i$, multiplicities $\mathrm{pos}_i, \mathrm{neg}_i \in \mathbb{N}$, and a degree-zero divisor $D_z$ equal to $\sum_{c_i = 0} (\mathrm{pos}_i - \mathrm{neg}_i)[w_i]$ whose class in $\mathrm{Pic}^0$ vanishes (i.e. $D_z$ is principal), the conclusion is that the tensor product, formed by folding over $i = 0,\dots,n-1$ and retaining only the indices with $c_i = 0$, of the dual of the module of the $\mathrm{pos}_i$-th power of the ideal sheaf of the graph of $z_i$ with the module of the $\mathrm{neg}_i$-th power of that ideal sheaf, starting from the monoidal unit, admits an isomorphism to the underlying module of the unit rigidified line bundle on $c$ with rigidification the base change of $\varepsilon_0$, namely the unit sheaf of modules on the fibre.
--
--   This is the statement that a divisor supported on $\kappa_A$-rational points of the level-$N_0$ special fibre whose class in $\mathrm{Pic}^0$ of the associated function field vanishes has trivial associated twisted line bundle, obtained from the Abel–Jacobi description of the Jacobian of the smooth proper curve model attached to the Deligne–Rapoport package. It is used in [`ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField`](thm.html#ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField), where vanishing of a divisor class must be converted into triviality of the corresponding bundle on the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
      {n : ℕ} (c : Fin n → Fin 2)

      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (w : Fin n → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀))
      (_ : ∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base ((z i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ = w i)
      (pos neg : Fin n → ℕ)
      (Dz : ↥(Divisor.degZero (K := (ResidueField ↥A)) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀))))
      (_ : (Dz : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 0), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)))
      (_ : Pic0.mk Dz = 0),
      Nonempty (((List.finRange n).foldr
          (fun i M => if c i = 0 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _)) ≅
        (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by sorry
