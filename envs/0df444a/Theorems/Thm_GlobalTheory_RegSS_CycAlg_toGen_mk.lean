-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_CycAlg_toGen_mk
-- name    : GlobalTheory.RegSS.CycAlg.toGen_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:54.568212+00:00
-- url     : https://prove2.me/theorems/fa313b85-42e6-4bdd-80f0-4e19d2551326
-- title:
--   Cyc Alg: to Gen mk
-- statement:
--   The Cyc Alg construction uses the to Gen mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L78-L80

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

theorem GlobalTheory.RegSS.CycAlg.toGen_mk (M : Matrix n n A) (p : A[X]) :
    toGen M (AdjoinRoot.mk _ p) = aeval (gen M) p := by sorry
