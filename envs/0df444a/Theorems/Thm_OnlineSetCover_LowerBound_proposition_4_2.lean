-- Prove2me | Theorems.Thm_OnlineSetCover_LowerBound_proposition_4_2
-- name    : OnlineSetCover.LowerBound.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:04:33.447982+00:00
-- url     : https://prove2.me/theorems/ec20c9f5-8dbf-4e29-a35a-58cfffd18b0a
-- title:
--   Proposition 4.2 — for $n \ge 2^{k+1}kr^2$ and $2^{2^k kr^2} \ge m \ge \binom{kr^2}{r}k^r$, every deterministic algorithm has competitive ratio $\ge kr$
-- statement:
--   For all positive integers $k, r$ and all $n, m$ satisfying
--
--   $$n \ge 2^{k+1} k r^2 \qquad\text{and}\qquad 2^{2^k k r^2} \;\ge\; m \;\ge\; \binom{kr^2}{r} k^r,$$
--
--   there is an instance of the unweighted online set cover problem with ground set $X = \{1, \dots, n\}$ and a family $\mathcal F$ of exactly $m$ distinct subsets of $X$ such that the competitive ratio of every deterministic online algorithm is at least $kr$. More precisely, for every valid deterministic online algorithm $A$ for $\mathcal F$ there is a nonempty arrival sequence $\sigma$ such that a single member of $\mathcal F$ contains every element of $\sigma$ (so $\mathrm{OPT}(\sigma) = 1$) and
--
--   $$|\mathcal C_A(\sigma)| \;\ge\; kr \;=\; kr\cdot\mathrm{OPT}(\sigma).$$
--
--   Choosing $r$ and $k$ as functions of $n$ and $m$ turns this into the paper's lower bound $\Omega\big(\log n \log m / (\log\log m + \log\log n)\big)$, nearly matching the $O(\log m \log n)$ upper bound of the paper's deterministic algorithm.
--
--   **Formalization Note** $X$ is `Fin n` and $\mathcal F$ a `Finset (Finset (Fin n))`, so its cardinality counts distinct sets. The conclusion states $\mathrm{OPT}(\sigma) = 1$ and cost $\ge kr$, which is how the paper establishes "competitive ratio at least $kr$"; since $\mathrm{OPT}(\sigma) = 1$ it gives $|\mathcal C_A(\sigma)| \ge kr \cdot \mathrm{OPT}(\sigma)$ with $\mathrm{OPT}(\sigma) \ge 1$. The family is asserted to exist, as in the paper; the construction behind it is the block family plus padding sets on the extra elements. Algorithms may add several sets per arrival.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 369, Proposition 4.2

import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game

namespace OnlineSetCover.LowerBound

/-- Proposition 4.2 (Alon et al. 2009, p. 369). For positive integers `k, r` and `n, m` with
`n ≥ 2^{k+1} k r²` and `2^{2^k k r²} ≥ m ≥ C(k r², r) k^r`, there is a family `𝓕` of exactly `m`
distinct subsets of `X = Fin n` such that against every valid deterministic online algorithm
`A` the adversary has a nonempty arrival sequence `σ` that a single member of `𝓕` covers
(`OPT(σ) = 1`) while `A` chooses at least `k r` sets; in particular the competitive ratio of
every deterministic online algorithm on `(X, 𝓕)` is at least `k r`. -/
theorem proposition_4_2 (k r n m : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hn : 2 ^ (k + 1) * k * r ^ 2 ≤ n)
    (hm_lo : (k * r ^ 2).choose r * k ^ r ≤ m)
    (hm_hi : m ≤ 2 ^ (2 ^ k * k * r ^ 2)) :
    ∃ 𝓕 : Finset (Finset (Fin n)), 𝓕.card = m ∧
      ∀ A : OnlineAlg (Fin n), IsValid 𝓕 A →
        ∃ σ : List (Fin n), σ ≠ [] ∧ (∃ S ∈ 𝓕, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by sorry

end OnlineSetCover.LowerBound
