-- Prove2me | Theorems.Thm_MarkovMixing_group_walk_reversal_distance
-- name    : MarkovMixing.group_walk_reversal_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:16:47.808402+00:00
-- url     : https://prove2.me/theorems/4aaf9540-57fd-444c-9295-a16ef45a0c01
-- title:
--   Lemma 4.13 -- a walk and its inverse walk mix at the same rate
-- statement:
--   Let $G$ be a finite group and $\mu$ a probability distribution on $G$. The **random walk on $G$ with increment distribution $\mu$** moves from $a$ to $ha$ with probability $\mu(h)$: at each step an increment $h\sim\mu$ is drawn and multiplied on the left. Its **time reversal** is the walk driven by the **inverse distribution** $\hat\mu(g)=\mu(g^{-1})$, which undoes $\mu$-steps. Write $u$ for the uniform distribution on $G$ and $\|\cdot\|_{TV}$ for the total variation distance, $\|\mu-\nu\|_{TV}=\max_{A\subseteq G}|\mu(A)-\nu(A)|$.
--
--   The theorem (Lemma 4.13 of Levin–Peres–Wilmer) asserts that the two walks approach uniformity at exactly the same speed: for every time $t$, the distribution after $t$ steps started at the identity satisfies
--   $$\bigl\|P^t(\mathrm{id},\cdot)-u\bigr\|_{TV}=\bigl\|\hat P^t(\mathrm{id},\cdot)-u\bigr\|_{TV},$$
--   where $P$ and $\hat P$ are the transition matrices of the $\mu$-walk and the $\hat\mu$-walk. Corollary 4.14 is immediate: a random walk on a group and its time reversal have the same mixing times. For card shuffling this means a shuffle and its inverse shuffle mix equally fast — the reason the riffle shuffle can be analyzed through the easier inverse riffle.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.6, Lemma 4.13 and Corollary 4.14, pp. 55-56

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Lemma 4.13 and Corollary 4.14** (LPW): a random walk on a finite group
and the walk with the inverse increment distribution (its time reversal) are
at the same total variation distance from the uniform distribution at every
time, so in particular they have the same mixing times. -/
theorem group_walk_reversal_distance {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) (t : ℕ) :
    tvDist (rowDist (groupWalk μ) t 1) (uniformDist G) =
      tvDist (rowDist (groupWalk (invDist μ)) t 1) (uniformDist G) := by
  sorry

end MarkovMixing
