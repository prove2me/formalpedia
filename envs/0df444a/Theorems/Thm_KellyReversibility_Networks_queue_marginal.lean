-- Prove2me | Theorems.Thm_KellyReversibility_Networks_queue_marginal
-- name    : KellyReversibility.Networks.queue_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:52:08.900005+00:00
-- url     : https://prove2.me/theorems/165d2215-30ed-4466-a270-ec32ad13d7ef
-- title:
--   Corollary 3.4 — queue $j$ is independent of the rest, with marginal $\pi_j$ and queue-length law (3.7)
-- statement:
--   Let an open network of queues with general customer routes (Section 3.1) satisfy the book's constraints, assume every series $b_j^{-1}=\sum_{n\ge0}a_j^n/\prod_{l=1}^n\phi_j(l)$ converges, and let $\pi(\mathbf C)=\prod_k\pi_k(\mathbf c_k)$ be the equilibrium distribution of Theorem 3.1. Fix a queue $j$. Then:
--   1. queue $j$ is in state $\mathbf c$ with probability $\pi_j(\mathbf c)$, i.e. $\sum_{\mathbf D:\,\mathbf d_j=\mathbf c}\pi(\mathbf D)=\pi_j(\mathbf c)$;
--   2. the state of queue $j$ is independent of the state of the rest of the system: for every $\mathbf C$,
--   $$\pi(\mathbf C)=\pi_j(\mathbf c_j)\sum_{\mathbf D:\ \mathbf d_k=\mathbf c_k\ (k\ne j)}\pi(\mathbf D);$$
--   3. the probability that queue $j$ contains $n$ customers is
--   $$P(n_j=n)=b_j\frac{a_j^n}{\prod_{l=1}^{n}\phi_j(l)}\qquad(3.7);$$
--   4. for a position $l\ge1$ and a class $(i,s)$ with $r(i,s)=j$,
--   $$P\big(n_j\ge l,\ c_j(l)=(i,s)\big)=\frac{\alpha_j(i,s)}{a_j}\,P(n_j\ge l),$$
--   so a customer in position $l$ of queue $j$ is a type-$i$ customer at stage $s$ of his route with probability $\alpha_j(i,s)/a_j$.
--
--   Equation (3.7) is what one would obtain for an isolated queue fed by a Poisson stream of rate $a_j$, although the arrivals at queue $j$ do not in general form a Poisson process.
--
--   **Formalization Note** Probabilities are sums of $\pi$ over sets of network states, written with `HasSum` (items 1–3) and with `tsum` over subtypes of a summable family (item 4). The conditional probability in item 4 is written in multiplied-out form. Types and queues are finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 63, Corollary 3.4, Eq. (3.7)

import Mathlib
import Definitions.Def_KellyReversibility_Networks_OpenNetwork
import Definitions.Def_KellyReversibility_Networks_ProductForm

namespace KellyReversibility.Networks

/-- **Corollary 3.4** (Kelly 1979, p. 63). Under the product-form equilibrium `π` of Theorem 3.1:
1. the state of queue `j` is `c` with probability `π_j(c)`;
2. the state of queue `j` is independent of the states of the other queues: `π(C)` is the
   product of the probability `π_j(c_j)` and the probability that the other queues are in the
   states `(c_k)_{k ≠ j}`;
3. queue `j` holds `n` customers with probability `b_j a_j^n / ∏_{l=1}^{n} φ_j(l)` (3.7);
4. for a position `l ≥ 1` and a class `x = (i, s)` at queue `j`, the probability that position `l`
   of queue `j` is occupied by a class-`x` customer is `α_j(i, s) / a_j` times the probability
   that queue `j` holds at least `l` customers. -/
theorem queue_marginal {I J : ℕ} (N : Network I J) (hN : N.IsValid)
    (hb : ∀ j : Fin J, Summable (fun n : ℕ => N.a j ^ n / N.phiProd j n)) (j : Fin J) :
    (∀ c : List (N.Cls j),
      HasSum (fun D : {D : N.State // D j = c} => N.netPi D) (N.queuePi j c)) ∧
    (∀ C : N.State, ∃ R : ℝ,
      HasSum (fun D : {D : N.State // ∀ k, k ≠ j → D k = C k} => N.netPi D) R ∧
      N.netPi C = N.queuePi j (C j) * R) ∧
    (∀ n : ℕ,
      HasSum (fun D : {D : N.State // (D j).length = n} => N.netPi D)
        (N.b j * N.a j ^ n / N.phiProd j n)) ∧
    (∀ (l : ℕ) (x : N.Cls j), 1 ≤ l →
      ∑' D : {D : N.State // (D j)[l - 1]? = some x}, N.netPi D =
        N.alpha j x.1.1 x.1.2 / N.a j *
          ∑' D : {D : N.State // l ≤ (D j).length}, N.netPi D) := by sorry

end KellyReversibility.Networks
