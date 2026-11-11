-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_theorem_1_1
-- name    : LewensteinGreedy.Competitive.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:03.833288+00:00
-- url     : https://prove2.me/theorems/f5e792e5-86e9-4dde-9031-9cc0c0655cf8
-- title:
--   Theorem 1.1 — Greedy is $O(\log\log n)$-competitive from every initial tree: $\mathrm{Greedy}(X,T_0)\le c\,(n+\mathrm{OPT}_n(X)\lambda(n))$
-- statement:
--   There is an absolute constant $c$ such that for every $n\ge1$, every initial BST $T_0$ on $[n]$ and every access sequence $X\in[n]^m$ (including the empty sequence),
--   $$\mathrm{Greedy}(X,T_0)\le c\,\bigl(n+\mathrm{OPT}_n(X)\,\lambda(n)\bigr),\qquad(1.1)$$
--   where $\mathrm{Greedy}(X,T_0)$ is the number of geometric touches of online geometric Greedy started from $T_0$ (initial points not charged), $\mathrm{OPT}_n(X)$ is the minimum node-touch cost of an offline BST execution serving $X$ with a freely chosen initial tree, and $\lambda(n)=1+\log_2\log_2(n+2)$.
--
--   Differences from the source:
--   - encoding: there is an absolute constant c → ∃ c : ℝ, 0 < c, chosen before every other quantifier; reason: the right-hand side is nonnegative, so a positive constant exists iff any constant does; uniformity is the source's "absolute"
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
--   - encoding: after an access every touched key gets one common height above all current heights (the time t for Greedy(X,T0); any common value in the generalized process of §2.2.2) → touched keys get max over [n] of the current heights plus 1 (greedyStep); reason: Lemma 2.2: only the weak order of heights matters; every admissible choice gives the same touch sets and cost
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Theorem 1.1, printed p. 2 / PDF 3

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy

namespace LewensteinGreedy.Competitive

/-- Theorem 1.1, printed p.2 / PDF 3: there is an absolute constant `c` such that for every
`n ≥ 1`, every initial BST `T₀` on `[n]` and every access sequence `X ∈ [n]^m` (`m = 0` allowed),
`Greedy(X, T₀) ≤ c (n + OPT_n(X) λ(n))`. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ T₀ : BinaryTree ℕ, SplayDynOpt.IsBSTOn n T₀ →
      ∀ X : List ℕ, ValidSequence n X →
        (greedyCost n X T₀ : ℝ) ≤ c * ((n : ℝ) + (OPT n X : ℝ) * lambda n) := by sorry

end LewensteinGreedy.Competitive
