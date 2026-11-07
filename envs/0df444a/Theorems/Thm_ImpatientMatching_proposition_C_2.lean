-- Prove2me | Theorems.Thm_ImpatientMatching_proposition_C_2
-- name    : ImpatientMatching.proposition_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:53:19.065646+00:00
-- url     : https://prove2.me/theorems/7bd9e2b2-6b84-4cf6-89ca-f2e13addf9b6
-- title:
--   Proposition C.2 — Finite-Zero finite-horizon upper bound
-- statement:
--   On the Finite-Zero construction with $L=9600$ and $a=(1+\varepsilon/2)K$, for every admissible policy $\pi$ and every $T>0$,
--   $$2\,\mathbb E M^\pi(T)\le[nL+\Gamma-\tau(H)]T,$$
--   and consequently
--   $$g^*\le nL-\frac{a+\tau(H)}{2}.$$
--
--   This is the upper bound of the Finite-Zero reduction.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Proposition C.2, (42) and (43), p.29

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Proposition C.2 (finite-horizon upper bound).** Yan–Varma, manuscript (sha256 7b1051b6…), (42) and (43), p.29: on the Finite-Zero
construction, `L = 9600`, every admissible policy and every `T > 0` satisfy
`2 E M^π(T) ≤ [nL + Γ − τ(H)]T`, and consequently `g∗ ≤ nL − (a + τ(H))/2`, with `a = (1 + ε/2)K`.

**Formalization Note.** The hypothesis `n ≥ n₀` is not needed. -/
theorem proposition_C_2 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) :
    (∀ π : MatchingPolicy, IsPaperPolicy (fzInstance H K) π → ∀ T : ℝ, 0 < T →
      2 * EM π T ≤
        ENNReal.ofReal (((H.N : ℝ) * (LFZ : ℝ) + (Gamma LFZ H K : ℝ) - (tau H : ℝ)) * T)) ∧
    gStar (fzInstance H K) ≤
      (((H.N : ℝ) * (LFZ : ℝ) - ((1 + (eps : ℝ) / 2) * (K : ℝ) + (tau H : ℝ)) / 2 : ℝ) : EReal) := by sorry

end ImpatientMatching
