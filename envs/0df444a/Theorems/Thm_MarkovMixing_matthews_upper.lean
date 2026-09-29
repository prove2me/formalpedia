-- Prove2me | Theorems.Thm_MarkovMixing_matthews_upper
-- name    : MarkovMixing.matthews_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:01:28.823178+00:00
-- url     : https://prove2.me/theorems/c7e272d5-2b28-4985-9799-05ff44d6fdbb
-- title:
--   Theorem 11.2 -- the Matthews upper bound on cover times
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with $n=|V|$ states. Write $\mathbb E_x(\tau_y)$ for the expected number of steps to reach $y$ from $x$, and define the two extremal quantities
--   $$t_{\mathrm{hit}}=\max_{x,y\in V}\ \mathbb E_x(\tau_y),\qquad t_{\mathrm{cov}}=\max_{x\in V}\ \mathbb E_x(\tau_{\mathrm{cov}}),$$
--   where $\tau_{\mathrm{cov}}$ is the **cover time** — the first time the chain has visited every state — so $t_{\mathrm{cov}}$ is the worst-case expected time to see the whole state space.
--
--   The theorem (the **Matthews method**, Theorem 11.2 of Levin–Peres–Wilmer) asserts:
--   $$t_{\mathrm{cov}}\;\le\;t_{\mathrm{hit}}\Bigl(1+\frac12+\cdots+\frac1n\Bigr).$$
--   Covering costs at most a harmonic-sum factor $\approx\log n$ beyond the worst single hitting time. The proof is a striking randomization trick: reveal the states in uniformly random order and bound the expected extra time to collect each new one; the $k$-th freshly revealed state is the last of $k$ to be visited with probability $1/k$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 11.2, Theorem 11.2, pp. 143-144

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **Theorem 11.2, the Matthews method** (LPW): for an irreducible chain on
`n` states, `t_cov ≤ t_hit (1 + 1/2 + ⋯ + 1/n)`. -/
theorem matthews_upper {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P) :
    coverTimeMax P ≤
      hitTimeMax P * ∑ k ∈ Finset.Icc 1 (Fintype.card V), (1 : ℝ) / k := by
  sorry

end MarkovMixing
