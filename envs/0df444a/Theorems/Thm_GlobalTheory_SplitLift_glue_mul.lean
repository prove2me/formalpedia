-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_glue_mul
-- name    : GlobalTheory.SplitLift.glue_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:23.718842+00:00
-- url     : https://prove2.me/theorems/62530036-c443-40b3-a160-e589fb75cf4f
-- title:
--   Split Lift: glue mul
-- statement:
--   The Split Lift construction uses the glue mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L211-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L211-L235

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

theorem GlobalTheory.SplitLift.glue_mul (s : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) {e : A}
    (he : e * e = e) (hes : e * s e = 0) {X X' : Matrix (Fin n) (Fin n) A}
    (hX : e • X = X) (hX' : e • X' = X') (h : X * X' = e • (1 : Matrix (Fin n) (Fin n) A)) :
    glue s J e X X' * glue s J e X' X = 1 := by sorry
