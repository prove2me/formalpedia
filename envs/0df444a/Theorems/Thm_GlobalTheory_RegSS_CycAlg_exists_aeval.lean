-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_CycAlg_exists_aeval
-- name    : GlobalTheory.RegSS.CycAlg.exists_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:59.244486+00:00
-- url     : https://prove2.me/theorems/fe934bf8-a97f-4b8d-a062-e3bd38e3cc81
-- title:
--   Cyc Alg: exists aeval
-- statement:
--   The Cyc Alg construction uses the exists aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L46-L48

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

theorem GlobalTheory.RegSS.CycAlg.exists_aeval {M : Matrix n n A} (l : genAlg M) :
    ∃ p : A[X], aeval M p = (l : Matrix n n A) := by sorry
