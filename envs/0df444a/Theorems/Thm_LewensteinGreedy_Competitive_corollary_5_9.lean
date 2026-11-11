-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_corollary_5_9
-- name    : LewensteinGreedy.Competitive.corollary_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:20.382231+00:00
-- url     : https://prove2.me/theorems/44bb6b89-a40d-4a74-b40f-ac978c4d9bef
-- title:
--   Corollary 5.9 — base competitiveness $C(X;h)=O((n+\mathrm{OPT}_n(X))\log\log n)$ for every initial profile
-- statement:
--   There is an absolute constant $c>0$ such that for every $n\ge1$, every access sequence $X\in[n]^m$ and every finite real initial height profile $h$ on $[n]$ (not necessarily encoding a BST),
--   $$C(X;h)\le c\,\bigl(n+\mathrm{OPT}_n(X)\bigr)\,\lambda(n).\qquad(5.15)$$
--
--   Differences from the source:
--   - reading: C(X;h) = O((n + OPT_n(X)) log log n) in O-notation, with log log s standing for λ(s) (§1.2) → explicit absolute constant chosen before n, X and the profile; λ written out; reason: §1.2 fixes this convention for all asymptotic bounds and §5.3 says "All constants are absolute"
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
--   - encoding: after an access every touched key gets one common height above all current heights (the time t for Greedy(X,T0); any common value in the generalized process of §2.2.2) → touched keys get max over [n] of the current heights plus 1 (greedyStep); reason: Lemma 2.2: only the weak order of heights matters; every admissible choice gives the same touch sets and cost
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Corollary 5.9, printed p. 38 / PDF 39

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy

namespace LewensteinGreedy.Competitive

/-- Corollary 5.9 (base competitiveness), printed p.38 / PDF 39: one absolute constant `c` with
`C(X; h) ≤ c (n + OPT_n(X)) λ(n)` for every `n ≥ 1`, every access sequence on `[n]` and every
real initial height profile `h`. -/
theorem corollary_5_9 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ X : List ℕ, ValidSequence n X →
      ∀ h : Profile,
        (cost n X h : ℝ) ≤ c * ((n : ℝ) + (OPT n X : ℝ)) * lambda n := by sorry

end LewensteinGreedy.Competitive
