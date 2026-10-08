-- Prove2me | Theorems.Thm_MNLBandit_LowerBound_theorem_2
-- name    : MNLBandit.LowerBound.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:30.142643+00:00
-- url     : https://prove2.me/theorems/24ca17ff-f5f5-425f-b116-a9bcffb746f8
-- title:
--   Theorem 2, p. 14 — under a K-cardinality constraint every policy has regret at least C√(NT/K) on a randomized instance
-- statement:
--   **Setting.** An MNL-Bandit instance with $n$ products consists of a no-purchase weight $v_0>0$, attraction parameters $v_i$ with $0\le v_i\le v_0$, and revenues $r_i\in[0,1]$. Offering an assortment $S$ yields one customer choice drawn from the MNL model $p_i(S)=v_i/(v_0+\sum_{j\in S}v_j)$ for $i\in S\cup\{0\}$, and the expected revenue $R(S,v)=\sum_{i\in S}r_iv_i/(v_0+\sum_{j\in S}v_j)$. A policy may be randomized; it respects the $K$-cardinality constraint if it only offers assortments with $|S^\pi_t|\le K$. Its regret over $T$ periods is
--
--   $$
--   \mathrm{Reg}_\pi(T,v)=\mathbb E_\pi\Big(\sum_{t=1}^{T}R(S^*,v)-R(S^\pi_t,v)\Big),
--   $$
--
--   where $S^*$ is an assortment of at most $K$ products with maximum expected revenue.
--
--   **Theorem.** There is an absolute constant $C>0$ such that for every number of products $n\ge2$, every $K$ with $1\le K\le n$ and every horizon $T\ge n$ there is a randomized instance, a probability distribution with finite support over instances $(v_0,v,r)$ satisfying $v_0\ge v_i$ and $r_i\in[0,1]$. The values of $v_0$ and $r$ are common to every point in the support, as in the paper's constructions. Every policy $\pi$ respecting the $K$-cardinality constraint has
--
--   $$
--   \mathbb E_{\text{instance}}\big[\mathrm{Reg}_\pi(T,v)\big]\ge C\sqrt{\frac{nT}{K}} .
--   $$
--
--   The randomized instance is chosen before the policy and may depend on $n$, $K$ and $T$ only. Together with the $O(\sqrt{nT\log nT})$ upper bound of Theorem 1 it shows that the epoch-based UCB policy is optimal up to logarithmic factors when $K$ is fixed.
--
--   **Formalization Note** The randomized instance is a finite list of instances with weights $w_j\ge0$ summing to $1$; the paper's instances (Definitions 5.2 and E.1) are uniform over finitely many values, so a finite support is faithful, and the regret is averaged over the instance as in Lemma 5.1. All support points share the same known revenues $r$ and no-purchase weight $v_0$, as those constructions do. Without this clause, one common policy would be tested on instances distinguished by revenues known to the seller, weakening the lower bound. Policies are behavioural: at every history of offered sets and choices they draw the next assortment from a probability vector, which by Kuhn's theorem covers the paper's admissible policies (2.4). The page says "for any $N$ and $K$"; the claim is false for $n=1$ (offering the single product whenever $r_1>0$ is optimal for every $v$) and for $K=0$ (only $\emptyset$ can be offered), so $n\ge2$ and $K\ge1$ are added; $K\le n$ is the cardinality constraint's range. $C>0$ is part of the claim.
-- source:
--   Agrawal, Avadhanula, Goyal, Zeevi, MNL-Bandit: A Dynamic Learning Approach to Assortment Selection, arXiv:1706.03880v2, p. 14, Theorem 2; model pp. 5–7, (2.1)–(2.6)

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_Setting

namespace MNLBandit.LowerBound

theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n K T : ℕ), 2 ≤ n → 1 ≤ K → K ≤ n → n ≤ T →
      ∃ (m : ℕ) (w : Fin m → ℝ) (inst : Fin m → Instance n),
        (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, (inst j).Valid) ∧
        (∀ j k, (inst j).v₀ = (inst k).v₀ ∧ (inst j).r = (inst k).r) ∧
        ∀ π : BPolicy n, IsCardinalityK K π →
          C * Real.sqrt ((n : ℝ) * T / K) ≤ ∑ j, w j * regret (inst j) K π T := by sorry

end MNLBandit.LowerBound
