-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_moore_step_sum
-- name    : GlobalTheory.PMonE.moore_step_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:39:58.500318+00:00
-- url     : https://prove2.me/theorems/99571faf-5df7-48a8-ada6-70ef82038093
-- title:
--   PMon E: moore step sum
-- statement:
--   The PMon E construction uses the moore step sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MoorePowSubSelfEqProd.lean#L71-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Polynomial

theorem GlobalTheory.PMonE.moore_step_sum {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {h : ℕ} (c : Fin h → ℤ)
    (x : Fin h → F) (t : F) :
    ∑ i, (c i : F) * (x i ^ p - t ^ (p - 1) * x i) =
      (∑ i, (c i : F) * x i) ^ p - t ^ (p - 1) * ∑ i, (c i : F) * x i := by sorry
