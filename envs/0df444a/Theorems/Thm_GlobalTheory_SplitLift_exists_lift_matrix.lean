-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_exists_lift_matrix
-- name    : GlobalTheory.SplitLift.exists_lift_matrix
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:14.061461+00:00
-- url     : https://prove2.me/theorems/8b79566f-cbf8-4507-9c0d-256c05df2b70
-- title:
--   Split Lift: exists lift matrix
-- statement:
--   The Split Lift construction uses the exists lift matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L13-L30

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

theorem GlobalTheory.SplitLift.exists_lift_matrix {S k : Type} [CommRing S] [Field k] (r : S →+* k) (ε : S)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (M : GL (Fin n) k) :
    ∃ N N' : Matrix (Fin n) (Fin n) S, N.map r = (M : Matrix (Fin n) (Fin n) k) ∧
      N * N' = ε • (1 : Matrix (Fin n) (Fin n) S) ∧ N' * N = ε • (1 : Matrix (Fin n) (Fin n) S) := by sorry
