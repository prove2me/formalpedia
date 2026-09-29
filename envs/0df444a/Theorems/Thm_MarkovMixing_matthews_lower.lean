-- Prove2me | Theorems.Thm_MarkovMixing_matthews_lower
-- name    : MarkovMixing.matthews_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:01:41.352791+00:00
-- url     : https://prove2.me/theorems/9adef152-3f7e-4020-8c43-7738e2c3ddff
-- title:
--   Proposition 11.4 -- the Matthews lower bound on cover times
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$. Write $\mathbb E_x(\tau_y)$ for the expected number of steps to reach $y$ from $x$, and
--   $$t_{\mathrm{cov}}=\max_{x\in V}\ \mathbb E_x(\tau_{\mathrm{cov}})$$
--   for the worst-case expected **cover time**, $\tau_{\mathrm{cov}}$ being the first time the chain has visited every state.
--
--   The theorem (the Matthews lower bound, Proposition 11.4 of Levin–Peres–Wilmer) asserts: for every set $A\subseteq V$ with at least two states and every $m\ge0$ below all hitting times within $A$ — that is, $m\le\mathbb E_a(\tau_b)$ for all distinct $a,b\in A$ —
--   $$t_{\mathrm{cov}}\;\ge\;m\,\Bigl(1+\frac12+\cdots+\frac1{|A|-1}\Bigr).$$
--   The randomized survey argument of the Matthews upper bound reverses: covering must in particular collect the hard-to-reach set $A$, and revealing $A$'s states in random order forces a harmonic sum of waiting times, each at least $m$. Choosing $A$ well (spread-out states with mutual hitting times close to $t_{\mathrm{hit}}$) makes upper and lower bounds match up to constants.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 11.3, Proposition 11.4, p. 145

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Proposition 11.4, the Matthews lower bound** (LPW): for any set `A` of
states and any `m` below all hitting times between distinct states of `A`,
`t_cov ≥ m (1 + 1/2 + ⋯ + 1/(|A|−1))`. -/
theorem matthews_lower {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (A : Finset V) (hA : 2 ≤ A.card) (m : ℝ) (hm : 0 ≤ m)
    (hmin : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → m ≤ expSetHitTime P a {b}) :
    m * ∑ k ∈ Finset.Icc 1 (A.card - 1), (1 : ℝ) / k ≤ coverTimeMax P := by
  sorry

end MarkovMixing
