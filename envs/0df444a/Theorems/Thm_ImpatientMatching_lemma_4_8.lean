-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_8
-- name    : ImpatientMatching.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:23.537396+00:00
-- url     : https://prove2.me/theorems/1dddd7e8-ecee-40a4-a47a-7794cd61ac57
-- title:
--   Lemma 4.8 — finite-horizon upper bound
-- statement:
--   On the Finite-Finite construction with $L=6000$ and $\varepsilon=1/100$, for every admissible policy $\pi$ and every $T>0$,
--   $$\frac1T\,\mathbb E\int_0^T\Phi(P(t))\,dt\le(1+\varepsilon/2)K+2(L+1)\bigl(\Gamma-r^\pi(T)\bigr),$$
--   and consequently
--   $$r^\pi(T)\le\Gamma-\frac{\tau(H)-(1+\varepsilon/2)K}{2(L+1)}.$$
--
--   This combines the two loss bounds with the covering inequality of Lemma 4.5.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ n₀ of the reduction → no such hypothesis; reason: the proof does not use (11); on n ≥ n₀ this is the source's statement
--   - encoding: (21) with 1/T and the rate r^π(T) on the right → (21) multiplied by T, with T r^π(T) = E M^π(T) moved to the left, in ℝ≥0∞; reason: the two forms are equivalent since the match count is finite
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.8, (21) and (22), p.15

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Lemma 4.8 (finite-horizon upper bound).** Yan–Varma, manuscript (sha256 7b1051b6…), (21) and (22), p.15: for every admissible policy
and every `T > 0`, `(1/T) E ∫₀ᵀ Φ(P(t)) dt ≤ (1 + ε/2)K + 2(L + 1)(Γ − r^π(T))`, and consequently
`r^π(T) ≤ Γ − (τ(H) − (1 + ε/2)K)/(2(L + 1))`.

**Formalization Note.** The first display is multiplied by `T`, with `T r^π(T) = E M^π(T)` moved to the
left in `ℝ≥0∞`. -/
theorem lemma_4_8 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) (π : MatchingPolicy)
    (hπ : IsPaperPolicy (ffInstance H K) π) (T : ℝ) (hT : 0 < T) :
    intPhi H (ffInstance H K) π T + ENNReal.ofReal (2 * ((LFF : ℝ) + 1)) * EM π T ≤
      ENNReal.ofReal (((1 + (eps : ℝ) / 2) * (K : ℝ) +
        2 * ((LFF : ℝ) + 1) * (Gamma LFF H K : ℝ)) * T) ∧
    rate (ffInstance H K) π T ≤
      (((Gamma LFF H K : ℝ) -
        ((tau H : ℝ) - (1 + (eps : ℝ) / 2) * (K : ℝ)) / (2 * ((LFF : ℝ) + 1)) : ℝ) : EReal) := by sorry

end ImpatientMatching
