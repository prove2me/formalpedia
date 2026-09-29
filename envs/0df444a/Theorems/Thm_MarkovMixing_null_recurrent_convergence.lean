-- Prove2me | Theorems.Thm_MarkovMixing_null_recurrent_convergence
-- name    : MarkovMixing.null_recurrent_convergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:41:11.038011+00:00
-- url     : https://prove2.me/theorems/3265087c-ef35-4443-a968-968348d5c14a
-- title:
--   Null recurrent chains: $P^t(x,y)\to 0$
-- statement:
--   Let $P$ be an irreducible Markov chain on a countable state space $V$ (nonnegative entries, rows summing to one as convergent series, every state reaching every other), and suppose the chain is **null recurrent**: some state $x_0$ is recurrent — return is certain, $\mathbb P_{x_0}\{\tau^+_{x_0}>t\}\to0$ — but not positive recurrent — the expected return time $\sum_{t\ge0}\mathbb P_{x_0}\{\tau^+_{x_0}>t\}$ diverges. (Simple random walk on $\mathbb Z$ or $\mathbb Z^2$ is the standard example.)
--
--   The theorem (Theorem 21.17 of Levin–Peres–Wilmer) asserts: for **all** states $x,y$,
--   $$P^t(x,y)\;\longrightarrow\;0\qquad(t\to\infty).$$
--
--   A null recurrent chain visits every state infinitely often, yet at any late fixed time it is nowhere in particular: the mass spreads out and no stationary profile is approached — consistent with this mission's equivalence, since a stationary distribution would force positive recurrence. Together with the positive-recurrent convergence theorem, this completes the trichotomy: transient chains escape, null recurrent chains return but diffuse away, positive recurrent chains converge to their stationary distribution.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 21.4, Theorem 21.17, Eq. (21.14), p. 283

import Definitions.Def_mm_countable

namespace MarkovMixing

/-- **Theorem 21.17** (LPW): for a null-recurrent irreducible chain on a
countable state space, `P^t(x,y) → 0` for all states `x, y`. -/
theorem null_recurrent_convergence {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P)
    (x₀ : V) (hrec : Recurrent P x₀) (hnull : ¬PositiveRecurrent P x₀)
    (x y : V) :
    Filter.Tendsto (fun t => stepPow P t x y) Filter.atTop (nhds 0) := by
  sorry

end MarkovMixing
