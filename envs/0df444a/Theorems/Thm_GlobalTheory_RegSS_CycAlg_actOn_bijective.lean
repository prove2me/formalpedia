-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_CycAlg_actOn_bijective
-- name    : GlobalTheory.RegSS.CycAlg.actOn_bijective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:25.572371+00:00
-- url     : https://prove2.me/theorems/b96e6cf2-6546-4a28-9f5b-fe6655117c3c
-- title:
--   Cyc Alg: act On bijective
-- statement:
--   The Cyc Alg construction uses the act On bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L59-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.CycAlg.actOn_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (actOn M v) := by sorry
