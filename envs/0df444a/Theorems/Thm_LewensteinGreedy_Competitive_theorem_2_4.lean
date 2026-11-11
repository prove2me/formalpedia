-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_theorem_2_4
-- name    : LewensteinGreedy.Competitive.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:57.934895+00:00
-- url     : https://prove2.me/theorems/67de6dda-b2b2-49c7-bb71-c77d97ab69cd
-- title:
--   Theorem 2.4 — comparator-relative bound $C(X;h)\le c\,(n+m+E)\,G$
-- statement:
--   There is an absolute constant $c>0$ such that for every $n\ge1$, every access sequence $X\in[n]^m$, every finite real initial height profile $h$ and every comparator serving $X$ (requested key at the root of its designated state; arbitrary initial tree, heights and rotation depths), with $E=\sum_i(1+d_i)$ and $G=1+\mathrm{bitlen}(H)$,
--   $$C(X;h)\le c\,(n+m+E)\,G .\qquad(2.4)$$
--
--   Differences from the source:
--   - encoding: there is an absolute constant c → ∃ c : ℝ, 0 < c, chosen before every other quantifier; reason: the right-hand side is nonnegative, so a positive constant exists iff any constant does; uniformity is the source's "absolute"
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
--   - encoding: after an access every touched key gets one common height above all current heights (the time t for Greedy(X,T0); any common value in the generalized process of §2.2.2) → touched keys get max over [n] of the current heights plus 1 (greedyStep); reason: Lemma 2.2: only the weak order of heights matters; every admissible choice gives the same touch sets and cost
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Theorem 2.4, printed p. 8 / PDF 9

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_rotateAt
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy
import Definitions.Def_LewensteinGreedy_Competitive_Comparator

namespace LewensteinGreedy.Competitive

/-- Theorem 2.4 (comparator-relative bound), printed p.8 / PDF 9: one absolute constant `c` with
`C(X; h) ≤ c (n + m + E) G` for every `n ≥ 1`, every access sequence `X` on `[n]`, every real
initial height profile `h` and every comparator serving `X`. -/
theorem theorem_2_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ X : List ℕ, ValidSequence n X →
      ∀ h : Profile, ∀ e : Comparator, e.serves n X →
        (cost n X h : ℝ) ≤
          c * ((n : ℝ) + (X.length : ℝ) + (e.energy : ℝ)) * (e.levels n : ℝ) := by sorry

end LewensteinGreedy.Competitive
