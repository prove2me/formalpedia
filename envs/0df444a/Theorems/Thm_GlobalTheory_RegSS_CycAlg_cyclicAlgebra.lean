-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_CycAlg_cyclicAlgebra
-- name    : GlobalTheory.RegSS.CycAlg.cyclicAlgebra
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:03.584873+00:00
-- url     : https://prove2.me/theorems/556845ad-8a29-4c22-ba58-82b908f2e5fb
-- title:
--   Cyc Alg: cyclic Algebra
-- statement:
--   The Cyc Alg construction uses the cyclic Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CyclicVectorGeneratedAlgebraStructure.lean#L94-L100

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

theorem GlobalTheory.RegSS.CycAlg.cyclicAlgebra : GlobalTheory.RegSS.CyclicAlgebra := by sorry
