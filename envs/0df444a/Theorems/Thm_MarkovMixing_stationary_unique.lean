-- Prove2me | Theorems.Thm_MarkovMixing_stationary_unique
-- name    : MarkovMixing.stationary_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:29.394389+00:00
-- url     : https://prove2.me/theorems/123b286f-a191-444c-aa5f-7ec56c3e3b7b
-- title:
--   Corollary 1.17 (uniqueness) -- at most one stationary distribution
-- statement:
--   An irreducible chain has at most one stationary distribution: if $\pi$ and $\pi'$ are both probability distributions fixed by $P$ ($\pi P=\pi$ and $\pi'P=\pi'$), then $\pi=\pi'$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.5.4, Corollary 1.17, p. 14

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Corollary 1.17** (LPW), uniqueness part: an irreducible chain has at most
one stationary distribution. -/
theorem stationary_unique {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π π' : V → ℝ) (hπ : IsStationary P π) (hπ' : IsStationary P π') :
    π = π' := by
  sorry

end MarkovMixing
