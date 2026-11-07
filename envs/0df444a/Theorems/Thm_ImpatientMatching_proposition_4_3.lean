-- Prove2me | Theorems.Thm_ImpatientMatching_proposition_4_3
-- name    : ImpatientMatching.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:32.415975+00:00
-- url     : https://prove2.me/theorems/881b3f5e-57e2-4c29-a7c0-ec05fcfcdcf0
-- title:
--   Proposition 4.3 — NO-instance bound
-- statement:
--   On the Finite-Finite construction, suppose $\tau(H)\ge(1+\varepsilon)K$. Then every admissible policy satisfies
--   $$r^\pi(T)\le\Gamma-\frac{\varepsilon K}{4(L+1)}\qquad(T>0),$$
--   hence
--   $$g^*\le\Gamma-\frac{\varepsilon K}{4(L+1)}.$$
--
--   This is the upper threshold $g_-$ of the value gap in Theorem 4.2.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Proposition 4.3, (13), p.12

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Proposition 4.3 (NO-instance bound).** Yan–Varma, manuscript (sha256 7b1051b6…), (13), p.12: if `τ(H) ≥ (1 + ε)K`, every admissible
policy has `r^π(T) ≤ Γ − εK/(4(L + 1))` for all `T > 0`, hence `g∗ ≤ Γ − εK/(4(L + 1))`.

**Formalization Note.** The hypothesis `n ≥ n₀` is not needed: only Lemma 4.10 uses it. -/
theorem proposition_4_3 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K)
    (hNo : (1 + (eps : ℝ)) * (K : ℝ) ≤ (tau H : ℝ)) :
    (∀ π : MatchingPolicy, IsPaperPolicy (ffInstance H K) π → ∀ T : ℝ, 0 < T →
      rate (ffInstance H K) π T ≤
        (((Gamma LFF H K : ℝ) - (eps : ℝ) * (K : ℝ) / (4 * ((LFF : ℝ) + 1)) : ℝ) : EReal)) ∧
    gStar (ffInstance H K) ≤
      (((Gamma LFF H K : ℝ) - (eps : ℝ) * (K : ℝ) / (4 * ((LFF : ℝ) + 1)) : ℝ) : EReal) := by sorry

end ImpatientMatching
