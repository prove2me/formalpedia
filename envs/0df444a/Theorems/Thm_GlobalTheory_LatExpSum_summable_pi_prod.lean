-- Prove2me | Theorems.Thm_GlobalTheory_LatExpSum_summable_pi_prod
-- name    : GlobalTheory.LatExpSum.summable_pi_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:47.16854+00:00
-- url     : https://prove2.me/theorems/bc70892c-1981-4010-8e4f-ec46eea9703b
-- title:
--   Lat Exp Sum: summable pi prod
-- statement:
--   The Lat Exp Sum construction uses the summable pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdea.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdea.lean#L29-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
noncomputable section
open GlobalTheory GlobalTheory.LatExpSum

theorem GlobalTheory.LatExpSum.summable_pi_prod {ι : Type} [Fintype ι] {f : ι → ℤ → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ι → ℤ => ∏ i, f i (n i) := by sorry
