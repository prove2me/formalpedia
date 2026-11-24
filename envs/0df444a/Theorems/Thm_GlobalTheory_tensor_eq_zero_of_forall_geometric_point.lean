-- Prove2me | Theorems.Thm_GlobalTheory_tensor_eq_zero_of_forall_geometric_point
-- name    : GlobalTheory.tensor_eq_zero_of_forall_geometric_point
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:05.119545+00:00
-- url     : https://prove2.me/theorems/14daec96-11c1-432c-b20c-7d93b5c2e34d
-- title:
--   Global Theory: tensor eq zero of forall geometric point
-- statement:
--   The Global Theory construction uses the tensor eq zero of forall geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorEqZeroOfForallGeometricPoint.lean#L19-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorEqZeroOfForallGeometricPoint.lean#L19-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory

theorem GlobalTheory.tensor_eq_zero_of_forall_geometric_point :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] [IsReduced (TensorProduct O F A)] (M : Type) [AddCommGroup M] [Module O M] [Module.Flat O M] (t : TensorProduct O A M), (∀ φ : A →ₐ[O] F, TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) t = 0) → t = 0 := by sorry
