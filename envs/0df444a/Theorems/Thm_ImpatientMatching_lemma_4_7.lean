-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_7
-- name    : ImpatientMatching.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:14.566062+00:00
-- url     : https://prove2.me/theorems/801fe6ec-a3d1-4bc5-8267-759e7d277aa6
-- title:
--   Lemma 4.7 — loss from uncovered edges
-- statement:
--   On the Finite-Finite construction with $L=6000$, for every admissible policy $\pi$ and every $T>0$,
--   $$\mathbb E M^\pi(T)\le\Gamma T-\frac{1}{1+2L}\,\mathbb E\int_0^T u(P(t))\,dt,$$
--   where $u(P(t))$ counts the source edges with both supplier endpoints empty at time $t$.
--
--   This bounds how many edges a policy can leave uncovered.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - encoding: an inequality with a subtraction on the right → the subtracted term is moved to the left, in ℝ≥0∞; reason: the integrals are nonnegative and the match count is finite, so the two forms are equivalent; ℝ≥0∞ has no default values
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.7, (20), p.13

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Lemma 4.7.** Yan–Varma, manuscript (sha256 7b1051b6…), (20), p.13: for every admissible policy and every `T > 0`,
`E M^π(T) ≤ ΓT − (1/(1 + 2L)) E ∫₀ᵀ u(P(t)) dt` on the Finite-Finite construction.

**Formalization Note.** In `ℝ≥0∞` the subtraction is moved to the left. -/
theorem lemma_4_7 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) (π : MatchingPolicy)
    (hπ : IsPaperPolicy (ffInstance H K) π) (T : ℝ) (hT : 0 < T) :
    EM π T + ENNReal.ofReal (1 / (1 + 2 * (LFF : ℝ))) * intUncovered H (ffInstance H K) π T ≤
      ENNReal.ofReal ((Gamma LFF H K : ℝ) * T) := by sorry

end ImpatientMatching
