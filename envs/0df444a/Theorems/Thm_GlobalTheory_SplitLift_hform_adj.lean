-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_hform_adj
-- name    : GlobalTheory.SplitLift.hform_adj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:28.329549+00:00
-- url     : https://prove2.me/theorems/74a0c878-28ea-4b96-99ee-47cf70f807e6
-- title:
--   Split Lift: hform adj
-- statement:
--   The Split Lift construction uses the hform adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L198-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L198-L205

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}

theorem GlobalTheory.SplitLift.hform_adj (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    hform s J x (adj s J X *ᵥ y) = hform s J (X *ᵥ x) y := by sorry
