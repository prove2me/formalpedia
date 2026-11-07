-- Prove2me | Theorems.Thm_ImpatientMatching_proposition_4_4
-- name    : ImpatientMatching.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:39.708672+00:00
-- url     : https://prove2.me/theorems/64b9d006-2da4-409c-a73d-fd999acdf2af
-- title:
--   Proposition 4.4 — YES-instance bound
-- statement:
--   On the Finite-Finite construction with $n\ge n_0$, suppose $\tau(H)\le K$. Then there is a deterministic stationary Markov policy $\pi_U$ such that
--   $$g^{\pi_U}\ge\Gamma-n\left(\frac{\varepsilon}{8(L+1)}-\frac{\sigma}{2}\right).$$
--
--   This is the lower threshold of the value gap in Theorem 4.2. The policy keeps one supplier in reserve on each vertex of a cover of size $K$.
--
--   Differences from the source:
--   - generalization: there exists a deterministic stationary Markov policy π_U → the policy follows coverRule U o, for a cover U of size exactly K and an assignment o, and coverRule is deterministic; reason: this is the policy of the source's proof, and it implies the existence claim
--   - encoding: fresh randomization → one Exp(1) coin per event, in a private coordinate of the seed space; reason: any randomization over the countable decision set is a measurable function of it
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Proposition 4.4, (14), p.12

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Proposition 4.4 (YES-instance bound).** Yan–Varma, manuscript (sha256 7b1051b6…), (14), p.12: if `τ(H) ≤ K` then there is a deterministic
stationary Markov policy `π_U` with `g^{π_U} ≥ Γ − n(ε/(8(L + 1)) − σ/2)`.

**Formalization Note.** The conclusion names the source's policy: `π_U` follows `coverRule U o` for a
cover `U` of size exactly `K` and an assignment `o`. -/
theorem proposition_4_4 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) (hn : n0FF ≤ H.N)
    (hYes : tau H ≤ K) :
    ∃ (U : Finset (Fin H.N)) (o : Fin (edgeCount H) → Fin H.N) (π : MatchingPolicy),
      U.card = K ∧ IsCoverAssignment H U o ∧ IsDeterministicRule (coverRule U o) ∧
      Realizes (ffInstance H K) (coverRule U o) π ∧
      (((Gamma LFF H K : ℝ) - (H.N : ℝ) * ((eps : ℝ) / (8 * ((LFF : ℝ) + 1)) - (sigmaFF : ℝ) / 2) :
        ℝ) : EReal) ≤ averageReward (ffInstance H K) π := by sorry

end ImpatientMatching
