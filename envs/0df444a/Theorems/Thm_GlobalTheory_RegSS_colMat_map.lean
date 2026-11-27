-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_colMat_map
-- name    : GlobalTheory.RegSS.colMat_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:33.125024+00:00
-- url     : https://prove2.me/theorems/c4243800-6207-533e-b1cb-9d61316cf8fa
-- title:
--   Reg SS: col Mat map
-- statement:
--   The Reg SS construction uses the col Mat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
omit [DecidableEq n]

theorem GlobalTheory.RegSS.colMat_map {B : Type} [CommRing B] (f : A →+* B) (c : n → Matrix n n A) (v : n → A) :
    (colMat c v).map f = colMat (fun j => (c j).map f) (fun i => f (v i)) := by sorry
