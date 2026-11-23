-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_Semilocal_krylov_map_ringHom
-- name    : GlobalTheory.RegSS.Semilocal.krylov_map_ringHom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:39.915803+00:00
-- url     : https://prove2.me/theorems/00b22ce9-6af9-4277-a8a5-8f93e445fc2b
-- title:
--   Semilocal: krylov map ring Hom
-- statement:
--   The Semilocal construction uses the krylov map ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorSemilocalOfCyclicVectorField.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorSemilocalOfCyclicVectorField.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS Matrix
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.Semilocal
open Matrix

theorem GlobalTheory.RegSS.Semilocal.krylov_map_ringHom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by sorry
