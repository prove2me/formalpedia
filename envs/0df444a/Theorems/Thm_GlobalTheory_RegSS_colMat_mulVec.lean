-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_colMat_mulVec
-- name    : GlobalTheory.RegSS.colMat_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:36.172448+00:00
-- url     : https://prove2.me/theorems/d314b99c-903f-5e5b-9f71-b5568837602b
-- title:
--   Reg SS: col Mat mul Vec
-- statement:
--   The Reg SS construction uses the col Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L20-L25

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

theorem GlobalTheory.RegSS.colMat_mulVec (c : n → Matrix n n A) (v a : n → A) :
    colMat c v *ᵥ a = (∑ j, a j • c j) *ᵥ v := by sorry
