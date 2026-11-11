-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_lemma_6_2
-- name    : LewensteinGreedy.Competitive.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:32:48.572545+00:00
-- url     : https://prove2.me/theorems/250d03ab-6294-4a27-8989-065ef466caf2
-- title:
--   Lemma 6.2 — inactive-gap loss budget $C(X;h)\le\Phi_A(h)-\Phi_A(h_f)+2C(Y;\bar h)-U$
-- statement:
--   Let $n\ge1$, let $X\in[n]^m$ be nonempty with $k$ distinct requested keys, let $h$ be any finite real profile and $h_f$ the profile after Greedy serves $X$ from $h$. Let $U$ be the total number of touches on active keys in the original execution, including keys touched when not requested. Then
--   $$C(X;h)\le \Phi_A(h)-\Phi_A(h_f)+2\,C(Y;\bar h)-U,\qquad(6.2)$$
--   and in particular $C(X;h)\le (n-k)+2\,C(Y;\bar h)-m$.
--
--   Differences from the source:
--   - encoding: inequalities among naturals with subtraction → both inequalities cast to ℤ; reason: no truncated subtraction; same instances
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
--   - encoding: geometric touches defined by empty closed rectangles with earlier points (§2.1.3) → touch set defined by the height-profile rule (2.1) (touches); reason: §2.2 shows the two coincide (only the highest point of each column matters); (2.1) is the source's own operational rule
--   - encoding: after an access every touched key gets one common height above all current heights (the time t for Greedy(X,T0); any common value in the generalized process of §2.2.2) → touched keys get max over [n] of the current heights plus 1 (greedyStep); reason: Lemma 2.2: only the weak order of heights matters; every admissible choice gives the same touch sets and cost
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Lemma 6.2, printed p. 39 / PDF 40

import Mathlib
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Greedy
import Definitions.Def_LewensteinGreedy_Competitive_Quotient

namespace LewensteinGreedy.Competitive

/-- Lemma 6.2 (inactive-gap loss budget), printed p.39 / PDF 40:
`C(X; h) ≤ Φ_A(h) − Φ_A(h_f) + 2 C(Y; h̄) − U` (6.2), and in particular
`C(X; h) ≤ (n − k) + 2 C(Y; h̄) − m`. -/
theorem lemma_6_2 (n : ℕ) (hn : 1 ≤ n) (X : List ℕ) (hX : ValidSequence n X) (hne : X ≠ [])
    (h : Profile) :
    (cost n X h : ℤ) ≤
        (visibilityPotential n X h : ℤ) - (visibilityPotential n X (profileAfter n X h) : ℤ) +
          2 * (cost (quotientSize n X) (quotientSequence n X) (quotientProfile n X h) : ℤ) -
          (activeTouches n X h : ℤ) ∧
    (cost n X h : ℤ) ≤
        ((n : ℤ) - (X.toFinset.card : ℤ)) +
          2 * (cost (quotientSize n X) (quotientSequence n X) (quotientProfile n X h) : ℤ) -
          (X.length : ℤ) := by sorry

end LewensteinGreedy.Competitive
