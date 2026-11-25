-- Prove2me | Theorems.Thm_GlobalTheory_sec_eq_zero_and_hom_eq_of_thickenings
-- name    : GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:24:42.069078+00:00
-- url     : https://prove2.me/theorems/02bd7dd8-99c5-463e-9db8-58ee213d8c6b
-- title:
--   Global Theory: sec eq zero and hom eq of thickenings
-- statement:
--   The Global Theory construction uses the sec eq zero and hom eq of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroAndHomEqOfThickenings.lean#L63-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroAndHomEqOfThickenings.lean#L63-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThickeningDetermines

theorem GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom], (∀ (N : LB H.left), N.IsLB → ∀ s : LB.Sec N, (∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) → ∀ j, s.f j = 0) ∧ (∀ (Y : Over (Spec (CommRingCat.of R))) [IsSeparated Y.hom] (f g : H ⟶ Y), (∀ n : ℕ, (fstG I n H).left ≫ f.left = (fstG I n H).left ≫ g.left) → f = g) := by sorry
