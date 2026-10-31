-- Prove2me | Theorems.Thm_MultiUnitProphet_balancing_price_exists
-- name    : MultiUnitProphet.balancing_price_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:08.959466+00:00
-- url     : https://prove2.me/theorems/4f0ca44a-c22a-4553-b2f8-4f0eae0e78d5
-- title:
--   §3, (3.3) — the balancing price $\pi$ exists
-- statement:
--   Let $k\ge1$ and let $\mathcal F$ be an instance with $n$ buyers. Then $p\mapsto\delta_k(X_p)$ is non-decreasing, $p\mapsto\mu_k(X_p)$ is non-increasing, $\mu_k(X_0)=1$ when $n\ge k$, and $\mu_k(X_p)\to0$ as $p\to\infty$. If every $F_t$ is atomless, both maps are continuous, and if moreover $n>k$ there is a price $\pi$ with
--
--   $$\delta_k(X_\pi)=\mu_k(X_\pi).\qquad(3.3)$$
--
--   This is the existence of the paper's pricing scheme.
--
--   **Formalization Note** Atomless is `NullSingletonClass (F t)` (every singleton has measure zero).
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - generalization: the standing atomless assumption of §2, p.7 → the monotonicity and limit clauses are stated for every instance, atoms allowed; reason: the statement holds verbatim with atoms when buyers buy at value ≥ p (X_p counts v_t ≥ p); atomless instances are a special case
--   - generalization: µ_k(X_p) goes from 1 at p = 0 (since n > k) → µ_k(X_0) = 1 whenever k ≤ n; reason: the value at 0 needs only n ≥ k; n > k is a special case
--   - reading: goes from 1 to 0 as the price goes from 0 to ∞ → µ_k(X_0) = 1 and µ_k(X_p) → 0 as p → ∞; reason: the two endpoint values used by the intermediate value theorem
--   - generalization: the WLOG assumptions n > k and P[v_t > 0] > 0 (§2, p.7) → the monotonicity, limit and continuity clauses are stated for every n and every instance (existence keeps n > k); reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §3, p.8, the paragraph after (3.3) ("The atomless assumption ensures that such a price always exists")

import Mathlib
import Definitions.Def_MultiUnitProphet_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **The balancing price `π` of (3.3) exists.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §3, p.8: "Observe that δk(Xp) is monotone non-decreasing in p and µ(Xp) is monotone
non-increasing in p. Moreover, µk(Xp) goes from 1 to 0 as the price goes from 0 to ∞ (since
n > k). The atomless assumption ensures that both δk(Xp) and µk(Xp) are continuous. The
intermediate value theorem then guarantees the existence of π."

For every instance and supply `k ≥ 1`: `p ↦ δ_k(X_p)` is monotone non-decreasing, `p ↦ µ_k(X_p)` is
monotone non-increasing, `µ_k(X_0) = 1` when `k ≤ n`, and `µ_k(X_p) → 0` as `p → ∞`. If every
`F_t` is atomless, both maps are continuous, and if moreover `n > k` some price `p` satisfies
`δ_k(X_p) = µ_k(X_p)`.

**Formalization Note.** `µ_k(X_0) = 1` is stated under `k ≤ n` (the paper: `n > k`). -/
theorem balancing_price_exists (k n : ℕ) (hk : 1 ≤ k) (F : Fin n → Measure ℝ)
    (hF : IsInstance F) :
    Monotone (delta k F) ∧ Antitone (mu k F) ∧ (k ≤ n → mu k F 0 = 1) ∧
    Tendsto (mu k F) atTop (𝓝 0) ∧
    ((∀ t, NullSingletonClass (F t)) → Continuous (delta k F) ∧ Continuous (mu k F)) ∧
    ((∀ t, NullSingletonClass (F t)) → k < n → ∃ p : ℝ, delta k F p = mu k F p) := by sorry

end MultiUnitProphet
