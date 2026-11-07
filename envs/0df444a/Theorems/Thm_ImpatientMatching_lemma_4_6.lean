-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_6
-- name    : ImpatientMatching.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:43.330098+00:00
-- url     : https://prove2.me/theorems/7ab8e4ad-e715-46ef-85e7-0803c07dc81a
-- title:
--   Lemma 4.6 — loss from occupied supplier vertices
-- statement:
--   On the Finite-Finite construction with $L=6000$, for every admissible policy $\pi$ and every $T>0$,
--   $$\mathbb E M^\pi(T)\le nLT-\mathbb E\int_0^T|P(t)|\,dt,$$
--   where $P(t)$ is the set of supplier vertices with a waiting agent at time $t$.
--
--   This bounds how many vertices a policy can keep occupied.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - encoding: an inequality with a subtraction on the right → the subtracted term is moved to the left, in ℝ≥0∞; reason: the integrals are nonnegative and the match count is finite, so the two forms are equivalent; ℝ≥0∞ has no default values
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.6, (19), p.13

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Lemma 4.6.** Yan–Varma, manuscript (sha256 7b1051b6…), (19), p.13: for every admissible policy and every `T > 0`,
`E M^π(T) ≤ nLT − E ∫₀ᵀ |P(t)| dt` on the Finite-Finite construction, `L = 6000`.

**Formalization Note.** In `ℝ≥0∞` the subtraction is moved to the left. -/
theorem lemma_4_6 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) (π : MatchingPolicy)
    (hπ : IsPaperPolicy (ffInstance H K) π) (T : ℝ) (hT : 0 < T) :
    EM π T + intOccupied (ffInstance H K) π T ≤
      ENNReal.ofReal ((H.N : ℝ) * (LFF : ℝ) * T) := by sorry

end ImpatientMatching
