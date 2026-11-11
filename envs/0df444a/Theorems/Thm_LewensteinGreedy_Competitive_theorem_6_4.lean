-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_theorem_6_4
-- name    : LewensteinGreedy.Competitive.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:55.618112+00:00
-- url     : https://prove2.me/theorems/6b21e606-796e-457d-a366-a4d0efa438d4
-- title:
--   Theorem 6.4 — active-alphabet refinement $\mathrm{Greedy}(X,T_0)\le\Phi_A(-\mathrm{depth}_{T_0})+c_0\,\mathrm{OPT}_n(X)\lambda(k)$
-- statement:
--   There is an absolute constant $c_0>0$ such that for every $n\ge1$, every initial BST $T_0$ on $[n]$ and every nonempty access sequence $X\in[n]^m$ with $k$ distinct requested keys,
--   $$\mathrm{Greedy}(X,T_0)\le \Phi_A(-\mathrm{depth}_{T_0})+c_0\,\mathrm{OPT}_n(X)\,\lambda(k);\qquad(6.5)$$
--   in particular $\Phi_A(-\mathrm{depth}_{T_0})\le n-k$, so $\mathrm{Greedy}(X,T_0)\le\max(1,c_0)\,\bigl(n+\mathrm{OPT}_n(X)\lambda(k)\bigr)$.
--
--   Differences from the source:
--   - encoding: there is an absolute constant c₀ → ∃ c₀ : ℝ, 0 < c₀, chosen before every other quantifier; reason: the right-hand side is nonnegative, so a positive constant exists iff any constant does; uniformity is the source's "absolute"
--   - reading: "so the cost is O(n + OPT_n(X) log log k)" → Greedy(X,T₀) ≤ max(1, c₀)·(n + OPT_n(X)·λ(k)) with the same c₀; reason: the explicit constant is the one the "in particular" derivation gives from (6.5) and Φ_A ≤ n − k; log log k means λ(k) by §1.2
--   - encoding: Φ_A(−depth_{T₀}) ≤ n − k → the same inequality cast to ℤ; reason: no truncated subtraction
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
--   - encoding: after an access every touched key gets one common height above all current heights (the time t for Greedy(X,T0); any common value in the generalized process of §2.2.2) → touched keys get max over [n] of the current heights plus 1 (greedyStep); reason: Lemma 2.2: only the weak order of heights matters; every admissible choice gives the same touch sets and cost
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Theorem 6.4, printed p. 41 / PDF 42

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy
import Definitions.Def_LewensteinGreedy_Competitive_Quotient

namespace LewensteinGreedy.Competitive

/-- Theorem 6.4 (active-alphabet refinement), printed p.41 / PDF 42: one absolute constant `c₀`
such that for every `n ≥ 1`, every initial BST `T₀` on `[n]` and every nonempty `X` on `[n]` with
`k` distinct requested keys, `Greedy(X, T₀) ≤ Φ_A(−depth_{T₀}) + c₀ OPT_n(X) λ(k)` (6.5); in
particular `Φ_A(−depth_{T₀}) ≤ n − k`, so `Greedy(X, T₀) ≤ max(1, c₀) (n + OPT_n(X) λ(k))`. -/
theorem theorem_6_4 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ T₀ : BinaryTree ℕ, SplayDynOpt.IsBSTOn n T₀ →
      ∀ X : List ℕ, ValidSequence n X → X ≠ [] →
        (greedyCost n X T₀ : ℝ) ≤
            (visibilityPotential n X (initialProfile T₀) : ℝ) +
              c₀ * (OPT n X : ℝ) * lambda X.toFinset.card ∧
        (visibilityPotential n X (initialProfile T₀) : ℤ) ≤ (n : ℤ) - (X.toFinset.card : ℤ) ∧
        (greedyCost n X T₀ : ℝ) ≤
            max 1 c₀ * ((n : ℝ) + (OPT n X : ℝ) * lambda X.toFinset.card) := by sorry

end LewensteinGreedy.Competitive
