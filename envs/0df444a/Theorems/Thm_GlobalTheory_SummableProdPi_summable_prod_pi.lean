-- Prove2me | Theorems.Thm_GlobalTheory_SummableProdPi_summable_prod_pi
-- name    : GlobalTheory.SummableProdPi.summable_prod_pi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:10.689221+00:00
-- url     : https://prove2.me/theorems/20f12977-e00b-44b3-80b1-6f1ba81e293e
-- title:
--   Summable Prod Pi: summable prod pi
-- statement:
--   The Summable Prod Pi construction uses the summable prod pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableProdPi.lean#L5-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableProdPi.lean#L5-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummableProdPi

theorem GlobalTheory.SummableProdPi.summable_prod_pi {J A : Type} [inst : Fintype J] (f : J → A → ℝ)
    (h0 : ∀ (j : J) (a : A), (0 : ℝ) ≤ f j a) (hs : ∀ j : J, Summable (f j)) :
    Summable fun (n : J → A) ↦ ∏ j : J, f j (n j) := by sorry
