-- Prove2me | Theorems.Thm_MarkovMixing_exists_pow_pos
-- name    : MarkovMixing.exists_pow_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:41:51.989387+00:00
-- url     : https://prove2.me/theorems/87bdf000-c844-4096-8cad-4fbe15c5f389
-- title:
--   Proposition 1.7 -- a positive power of an irreducible aperiodic chain
-- statement:
--   If the stochastic matrix $P$ is irreducible and aperiodic, then there is an integer $r>0$ such that every entry of $P^r$ is strictly positive: $P^r(x,y)>0$ for all states $x,y$. This is the number-theoretic heart of the Convergence Theorem.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.3, Proposition 1.7, p. 8

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Proposition 1.7** (LPW): if `P` is irreducible and aperiodic, then some
power of `P` has all entries strictly positive. -/
theorem exists_pow_pos {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (hap : Aperiodic P) :
    ∃ r : ℕ, 0 < r ∧ ∀ x y : V, 0 < (P ^ r) x y := by
  sorry

end MarkovMixing
