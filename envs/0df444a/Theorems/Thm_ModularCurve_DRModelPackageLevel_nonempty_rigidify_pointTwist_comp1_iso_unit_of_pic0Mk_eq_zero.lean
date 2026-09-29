-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
-- name    : ModularCurve.DRModelPackageLevel.nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/037b43e4-c1b7-5dce-8013-db5a53d66c99
-- title:
--   Point twists of trivial divisor class are rigidly trivial
-- statement:
--   Fix $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion of $A$ is the structure map $R_p \to \overline{\mathbb{Q}}$; the residue field $\kappa = \mathrm{ResidueField}\,A$ then has characteristic $p$ and is an $R_p$-algebra via $\rho$ followed by the residue map. Assume the base change $c$ of `toBase0 N₀ p : X0 N₀ p ⟶ Spec (R p)` along $R_p \to \kappa$ is proper, and let $\varepsilon_0$ be a section of `toBase0 N₀ p` over $\mathrm{Spec}\,R_p$. Let $n$ be given, together with labels $c_i \in \mathbb{Z}/2$, $\kappa$-points $z_i$ of the fibre (morphisms $\mathrm{Spec}\,\kappa \to$ the pullback with $z_i$ followed by $c$ the identity), places $w_i$ of $\kappa \subseteq$ `modularFunctionFieldC κ N₀`, and the hypothesis that for each $i$ the image of the closed point of $\mathrm{Spec}\,\kappa$ under $z_i$, transported by the inverse of $\mathfrak{P}$'s comparison isomorphism `efib`, is a closed point of the curve model $\mathfrak{P}.\mathrm{Mfib}$ whose associated place is $w_i$. Let $\mathrm{pos}_i, \mathrm{neg}_i \in \mathbb{N}$, and let $D$ be a degree-zero divisor equal to $\sum_{c_i = 1} (\mathrm{pos}_i - \mathrm{neg}_i)\,[w_i]$ whose class in $\mathrm{Pic}^0$ vanishes, i.e. $D$ is the divisor of a nonzero function. The conclusion asserts the existence of an isomorphism of modules on the pullback of $c$ along $\mathrm{id}_{\mathrm{Spec}\,\kappa}$ between, on one side, the `rigidify` of the iterated tensor product over `List.finRange n` which for each $i$ with $c_i = 1$ inserts the dual of the $\mathrm{pos}_i$-th power of the ideal sheaf of the graph of $z_i$ tensored with the $\mathrm{neg}_i$-th power of that ideal sheaf (and does nothing when $c_i \neq 1$), starting from the unit object, the rigidification being taken along `rigSection` of $c$, $\mathrm{id}$ and the base change of $\varepsilon_0$, with the projection `pullback.snd`; and, on the other side, the underlying module of the unit rigidified line bundle, that is the structure sheaf.
--
--   This is the "principal implies trivial" step for point twists on the fibre at $A$ of the level-$N_0$ Deligne–Rapoport model: a divisor supported on the marked $\kappa$-points whose class in $\mathrm{Pic}^0$ of the modular function field vanishes yields a rigidified line bundle isomorphic to the trivial one, the transfer being made through the Abel–Jacobi description of the relative Picard functor of a smooth proper curve. It is used in the computation of the reduction of the quantity attached to the glue data of a $\mathrm{Pic}^0$-pair over the residue field, in [`ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField`](thm.html#ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.lean

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

theorem ModularCurve.DRModelPackageLevel.nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
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
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)))
      (_ : Pic0.mk Dz = 0),
      Nonempty ((Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
          (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) ((List.finRange n).foldr
          (fun i M => if c i = 1 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _))) ≅
        (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by sorry
