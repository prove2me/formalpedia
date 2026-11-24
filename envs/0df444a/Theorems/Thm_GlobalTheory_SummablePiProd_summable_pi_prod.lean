-- Prove2me | Theorems.Thm_GlobalTheory_SummablePiProd_summable_pi_prod
-- name    : GlobalTheory.SummablePiProd.summable_pi_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:20.601734+00:00
-- url     : https://prove2.me/theorems/f0e4ea50-d87f-404e-83a8-1aaafcaebf1e
-- title:
--   Summable Pi Prod: summable pi prod
-- statement:
--   The Summable Pi Prod construction uses the summable pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummablePiProd.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummablePiProd.lean#L7-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummablePiProd
universe u_1 u_2

theorem GlobalTheory.SummablePiProd.summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by sorry
