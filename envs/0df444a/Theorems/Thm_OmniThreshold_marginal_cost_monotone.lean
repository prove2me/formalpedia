-- Prove2me | Theorems.Thm_OmniThreshold_marginal_cost_monotone
-- name    : OmniThreshold.marginal_cost_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:57.816915+00:00
-- url     : https://prove2.me/theorems/bbedb4a5-4987-419b-bc55-3d45eaa4626c
-- title:
--   Proof of Theorem 2, p.10 — the marginal fulfillment cost of an order grows with the set of orders
-- statement:
--   Let $s_{ji}\ge0$ and $s_{ji}<c_i$. Fix the inventories and in-store demands, and let $V_2(a)$ be the optimal value of LP (2) when $a_i$ orders are accepted at location $i$. If $a\le b$ coordinatewise, then for every location $i$,
--   $$
--   V_2(a+e_i)-V_2(a)\le V_2(b+e_i)-V_2(b),
--   $$
--   where $e_i$ is the $i$-th unit vector. In the paper's words, the marginal cost of fulfilling an order $o$ in addition to a set of orders $O$ is at least as large as its marginal cost in addition to any subset of $O$.
--
--   **Formalization Note** A set of orders enters LP (2) only through the number of orders at each location. So $O$ is the count vector $b$, a subset of $O$ is a count vector $a\le b$, and $o$ is an order at a location $i$. The location $i$ may already have orders in $a$ or $b$. This same-location case is coordinatewise discrete convexity. The proof of Theorem 2 needs it, and it is not part of Lemma 1's distinct-coordinate supermodularity.
--
--   Differences from the source:
--   - encoding: sets of orders $O$, a subset, an order $o$ → count vectors $b$ and $a\le b$, and a unit vector $e_i$; reason: LP (2) depends on a set of orders only through its counts per location
--   - generalization: a single cancellation cost $c>\max\{s_{ji}\}$ → per-location costs with $s_{ji}<c_i$; reason: LP (2) has per-location $c_i$; the paper's assumption is the case $c_i=c$
--   - reading: shipping costs (no sign stated) → $s_{ji}\ge0$; reason: they are costs in the model of §1.1
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, proof of Theorem 2, p.10, "An immediate consequence of Lemma 1 is that the marginal cost of fulfilling an order o …"

import Mathlib
import Definitions.Def_OmniThreshold_lp2Value

namespace OmniThreshold

/-- **Proof of Theorem 2, p.10: marginal fulfillment costs grow with the set of orders** (Jia,
Karp, Ravi & Tayur, *Effective Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN
3932692, proof of Theorem 2, p.10: "An immediate consequence of Lemma 1 is that the marginal cost of
fulfilling an order `o` in addition to a set of orders `O`, the difference between the minimum
possible fulfillment cost of some set of orders `O` and the minimum possible fulfillment cost of
orders `O + {o}`, is at least as large as the marginal cost of fulfilling order `o` in addition to
any subset of `O`").

Let `V₂(a)` be the optimal value of LP (2) when `a_i` orders are accepted at location `i`, with the
inventory `I` and in-store demand `D^P` fixed. If `a ≤ b` coordinatewise (the orders `a` are a
subset of the orders `b`), then for every location `i` of the extra order `o`,
`V₂(a + e_i) − V₂(a) ≤ V₂(b + e_i) − V₂(b)`.

**Formalization Note** A set of orders enters LP (2) only through its count vector of locations,
so `O` is `b`, its subset is `a ≤ b`, and `o` is a unit vector `e_i = Pi.single i 1`. The location
`i` may already carry orders of `a` or `b`: the claim covers the same-location case, which the
proof of Theorem 2 needs and which is coordinatewise discrete convexity, not only the
distinct-coordinate supermodularity of Lemma 1. -/
theorem marginal_cost_monotone {n : ℕ} (I : Fin n → ℕ) (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (hs : ∀ i j, 0 ≤ s j i) (hsc : ∀ i j, s j i < c i) (DP : Fin n → ℕ) (a b : Fin n → ℕ)
    (hab : a ≤ b) (i : Fin n) :
    lp2Value c s I DP (a + Pi.single i 1) - lp2Value c s I DP a ≤
      lp2Value c s I DP (b + Pi.single i 1) - lp2Value c s I DP b := by sorry

end OmniThreshold
