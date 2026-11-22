-- Prove2me | Theorems.Thm_IterationSequence
-- name    : IterationSequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:32.833044+00:00
-- url     : https://prove2.me/theorems/23ffbbee-deea-450b-9575-8c5ec8e3914e
-- title:
--   Iteration Sequence: Iteration Sequence
-- statement:
--   The radii of the paper's main iteration (paper lines 228-247), built as a TOTAL recursion
--   with a guarded step.
--
--   The paper's construction is PARTIAL: `R_0 = 1`, and `R_{l+1} = R_l rho_i` is defined only when
--   the continuation condition `|Dv_l(0)| <= delta` holds, the construction stopping otherwise.
--   Lean will not accept a sequence undefined past a stopping index.  The resolution is to make the
--   recursion total by STALLING: at a radius where `Good` or `Cont` fails the step returns the same
--   radius.  Stalling preserves `Good`, so `Good (R l)` holds for EVERY `l`, and the two-sided
--   bound on `R (l+1)` is asserted only under `Cont (R l)`, so it is vacuous exactly where the
--   chain stalls.  That is faithful to the paper, which itself says the bounds involving `R_{l+1}`
--   "apply whenever the next scale is constructed".
--
--   `Good` is the normalization package carried at each scale and `Cont` the continuation
--   condition; the consumer instantiates them as
--   `Good R = (∀ y, ‖y‖ < R → |v y| ≤ R ^ sigma)` and
--   `Cont R = (R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta)`, which is how `IterationStep` supplies
--   the hypothesis `hstep`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationSequence.lean#L20-L48
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationSequence.lean#L20-L48

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IterationSequence
set_option autoImplicit false

theorem IterationSequence (Good Cont : ℝ → Prop) (θ : ℝ)
    (hGood1 : Good 1)
    (hstep : ∀ R : ℝ, Good R → Cont R → ∃ R' : ℝ, Good R' ∧ θ * R ≤ R' ∧ R' ≤ R / 4) :
    ∃ R : ℕ → ℝ, R 0 = 1 ∧ (∀ l : ℕ, Good (R l)) ∧
      ∀ l : ℕ, Cont (R l) → (θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) := by sorry
