-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_sec_nonzero_on_special_fibre
-- name    : GlobalTheory.exists_smul_sec_nonzero_on_special_fibre
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:00:42.34378+00:00
-- url     : https://prove2.me/theorems/418b0471-e0c6-4c05-a59c-acac15b6f60a
-- title:
--   Global Theory: exists smul sec nonzero on special fibre
-- statement:
--   The Global Theory construction uses the exists smul sec nonzero on special fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L369-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L369-L398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory.PrimSec

theorem GlobalTheory.exists_smul_sec_nonzero_on_special_fibre : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull j), (∃ i, σ.f i ≠ 0) → ∃ (c : K) (s : LB.Sec M), c ≠ 0 ∧ (∀ i, (j.app (M.U i)).hom (s.f i) = cst fK (j ⁻¹ᵁ M.U i) c * rs XK (le_pull M j le_rfl) (σ.f (fun _ => i))) ∧ ∃ x ∈ Out.nonzeroLocus s, f x = IsLocalRing.closedPoint O := by sorry
