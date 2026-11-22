-- Prove2me | Theorems.Thm_IterationDichotomy
-- name    : IterationDichotomy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:13:29.52808+00:00
-- url     : https://prove2.me/theorems/7b4611d7-2fae-4903-9c46-ce7bf5ccfd0f
-- title:
--   Iteration Dichotomy: Iteration Dichotomy
-- statement:
--   The dichotomy of the paper's main iteration (paper lines 247-255), stated for a chain of
--   radii supplied as a HYPOTHESIS rather than rebuilt: `IterationSequence` constructs such a
--   chain and `IterationStep` supplies its guarded step, so this node consumes the chain and
--   extracts the two branches the main proof then treats separately.
--
--   Writing `sigma` for the paper's `k + beta` and `Cont R` for the continuation condition
--   `R ^ (1 - sigma) * ‖gradient v 0‖ ≤ delta`, which is the paper's `|Dv_l(0)| ≤ delta` expressed
--   through `v` and the radius, the three conclusions are the paper's three assertions:
--
--   1. the iteration continues indefinitely exactly when `Dv(0) = 0`.  One direction is immediate;
--      the other is the paper's argument that an infinite iteration forces `R_l → 0` and hence
--      `|Dv_l(0)| → ∞`, since `sigma > 1`, contradicting the continuation condition;
--   2. in the infinite branch, `R_l → 0` and `v` decays at the paper's rate,
--      `|v y| ≤ theta^(-sigma) * r^sigma` for `‖y‖ < r` and every `0 < r ≤ 1` — the paper states it
--      between consecutive constructed scales, and choosing the scale for a given `r` gives it for
--      all `r` at once, which is the form eq:approximation needs;
--   3. in the finite branch there is a LEAST index `L` at which the continuation condition fails,
--      which is the `L` the paper introduces before applying lem:noncritical to `v_L`.
--
--   The hypothesis `hsand` is guarded by the continuation condition, exactly as
--   `IterationSequence` delivers it, so nothing is assumed about `R (l+1)` where the chain
--   stalls.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationDichotomy.lean#L25-L121
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/IterationDichotomy.lean#L25-L121

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IterationDichotomy
set_option autoImplicit false

theorem IterationDichotomy (σ δ θ : ℝ) (hσ : 1 < σ) (hδ : 0 < δ) (hθ0 : 0 < θ)
    (v : Plane → ℝ) (R : ℕ → ℝ) (hR0 : R 0 = 1) (hRpos : ∀ l : ℕ, 0 < R l)
    (hGood : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ σ)
    (hsand : ∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ →
        θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) :
    ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) ↔ gradient v 0 = 0)
      ∧ ((∀ l : ℕ, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) →
          Filter.Tendsto R Filter.atTop (nhds 0)
            ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ y : Plane, ‖y‖ < r → |v y| ≤ θ ^ (-σ) * r ^ σ)
      ∧ (gradient v 0 ≠ 0 →
          ∃ L : ℕ, ¬ (R L ^ (1 - σ) * ‖gradient v 0‖ ≤ δ)
            ∧ ∀ l < L, R l ^ (1 - σ) * ‖gradient v 0‖ ≤ δ) := by sorry
