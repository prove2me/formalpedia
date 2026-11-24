-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_exists_small_val
-- name    : GlobalTheory.UnitLemma.exists_small_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:52.188+00:00
-- url     : https://prove2.me/theorems/c44060c7-caa7-42e3-b329-c59afd8a4443
-- title:
--   Unit Lemma: exists small val
-- statement:
--   The Unit Lemma construction uses the exists small val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallConjFixedOfValuation.lean#L34-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.exists_small_val (K : UQ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : K.O, K.Small t ∧ val K.O (algebraMap K.O K.E t) = k := by sorry
