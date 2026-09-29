-- Prove2me | Theorems.Thm_OnlinePrimalDual_Routing_per_copy_guarantee
-- name    : OnlinePrimalDual.Routing.per_copy_guarantee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:49:34.483734+00:00
-- url     : https://prove2.me/theorems/547cd0e3-814a-4855-9cdf-b85e2aba3d29
-- title:
--   Lemma 9.1 — a single graph copy's bandwidth and load guarantee (milestone)
-- statement:
--   Part (i): given the weak-duality contradiction bound (bandwidth routed via shortest-path
--   routing is at least M − uMin) and the greedy fill guarantee of the capacity-limited routing
--   step, the total bandwidth accepted in a copy is at least M (out of Nj). Part (ii): given the
--   multiplicative-update invariant x(e,j) ≤ 2, the bandwidth routed via shortest-path routing on
--   any edge is at most uCap·(2 + 6·log₂ n), matching "the load on each edge in Gj is O(log n)"
--   with the explicit constant the proof derives. Requires `1 ≤ uCap` (added per moderation,
--   2026-09-21: the book's edge capacities are positive integers, u(e,j) ≥ 1, which the proof's
--   own `2^x ≤ 1+x` step for `x=1/uCap` needs; without it the conclusion is false for `uCap < 1`).
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 202-204, Lemma 9.1

import Mathlib

namespace OnlinePrimalDual.Routing

/-- **Lemma 9.1** (p. 202-204, PDF p. 113-115, milestone). A single copy `Gj`'s guarantee,
combining both parts of the book's lemma via the two facts its proof actually establishes.

Part (i) (bandwidth `≥ M`): the algorithm routes bandwidth `stepB` via shortest-path routing
(step (1b)) and `stepC` via capacity-limited arbitrary-path routing (step (1c)); `accepted =
stepB + stepC`. `hweak_duality` is the book's own contradiction argument ("Assume to the
contrary that the algorithm routes in step (1b) a total bandwidth `M′ < M − u(min,j)`... `M−M′`
is at most `u(min,j)`", p. 203) — i.e. `stepB ≥ M − uMin`; `hstepC_fills` is step (1c)'s own
greedy rule (route "if the total bandwidth routed in this step in `Gj` is less than `u(min,j)`",
p. 202, capped at `uMin` in total, p. 203's remark "at least `M−M′` (or zero...) are routed in
`Gj` in step (1c)"): `stepC ≥ min uMin (M − stepB)`. Together these give `M ≤ stepB + stepC`.

Part (ii) (load `O(log n)`): `hx_bound` is the invariant `x(e,j) ≤ 2` the algorithm's
multiplicative update never exceeds (p. 203, "The algorithm never routes requests in step (1b)
on edges with `x(e,j) > 1`, thus, `x(e,j) ≤ 2`"), with `x(e,j)`'s own closed form — initial value
`uMin/(m·uCap)`, multiplied by `1+1/uCap` once per request routed on the edge (p. 203) — evaluated
at `R`, the bandwidth routed via step (1b) on the edge. `huCap_le` is the copy construction's own
bound `u(e,j) ≤ m²·u(min,j)` (p. 203, used in the book's own `n`-conversion). The conclusion is
the book's own derivation solved for `R` exactly: from
`(uMin/(m·uCap))·exp((ln2/uCap)·R) ≤ (uMin/(m·uCap))·(1+1/uCap)^R ≤ 2` (the displayed chain, p.
203) and `exp((ln2/uCap)·R) = 2^(R/uCap)`, `R/uCap ≤ log₂(2m·uCap/uMin) = 1+log₂(m·uCap/uMin)`, so
`R ≤ uCap·(1+log₂(m·uCap/uMin))`; adding the step-(1c) contribution on the same edge (at most
`uMin ≤ uCap`, p. 204's closing line) gives total edge bandwidth `≤ uCap·(2+log₂(m·uCap/uMin))`,
and `m·uCap/uMin ≤ m·m² = m³` (from `huCap_le`) gives `log₂(m·uCap/uMin) ≤ 3log₂ m`; `hmn`
(`m ≤ n²`, the book's own `n`-conversion fact, p. 203, "Since `u(e,j) ≤ m²u(min,j)`, the latter
expression is equal to `u(e,j)O(log n)`") gives `log₂ m ≤ 2log₂ n`, so the total is
`≤ uCap·(2+6log₂ n)`, matching "the load on each edge in `Gj` is `O(log n)`" with the explicit
constant this proof derives.

**Hypothesis added per `CHANGES_REQUESTED.md` (moderation, 2026-09-21)**: `huCap_ge_one : 1 ≤
uCap`. The book's edge capacities are `u : E → ℕ` (p. 198), so `u(e,j) = uCap` is always a
positive *integer*, hence `≥ 1`; the proof's own step `2^{1/uCap} ≤ 1 + 1/uCap` (the elementary
fact `2^x ≤ 1+x` for `x ∈ [0,1]`) needs `1/uCap ≤ 1`, i.e. `uCap ≥ 1`. `huCap_pos : 0 < uCap`
alone permits `uCap < 1`, under which part (ii)'s conclusion is false (counterexample recorded in
`SELF_REVIEW.md`); `huCap_ge_one` closes that gap and is not a weakening — it is the book's own
integrality fact, previously left implicit. -/
theorem per_copy_guarantee
    (M uMin stepB stepC : ℝ)
    (huMin_pos : 0 < uMin) (hstepB_nonneg : 0 ≤ stepB) (hstepC_nonneg : 0 ≤ stepC)
    (hstepC_le_uMin : stepC ≤ uMin)
    (hweak_duality : M - uMin ≤ stepB)
    (hstepC_fills : min uMin (M - stepB) ≤ stepC)
    (uCap m n R : ℝ)
    (hm_pos : 0 < m) (hn_pos : 0 < n) (huCap_pos : 0 < uCap) (huCap_ge_one : 1 ≤ uCap)
    (hmn : m ≤ n ^ 2) (huCap_le : uCap ≤ m ^ 2 * uMin)
    (hR_nonneg : 0 ≤ R) (hx_bound : uMin / (m * uCap) * (1 + 1 / uCap) ^ R ≤ 2) :
    M ≤ stepB + stepC ∧ R ≤ uCap * (2 + 6 * Real.logb 2 n) := by sorry

end OnlinePrimalDual.Routing
