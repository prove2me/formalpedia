-- Prove2me | Theorems.Thm_ImpatientMatching_proposition_C_3
-- name    : ImpatientMatching.proposition_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:52:45.412962+00:00
-- url     : https://prove2.me/theorems/fdf38f6b-c393-42e7-b967-d126066957fc
-- title:
--   Proposition C.3 — Finite-Zero reward from a small cover
-- statement:
--   On the Finite-Zero construction with $L=9600$ and $n\ge n_0=8\cdot10^{10}$, if $\tau(H)\le K$, there is a deterministic stationary Markov policy $\pi_U$ such that
--   $$g^{\pi_U}\ge\Gamma-\frac{4m}{L}-\frac{\varepsilon n}{32},$$
--   where $m$ is the number of edges of $H$.
--
--   This is the lower bound of the Finite-Zero reduction.
--
--   Differences from the source:
--   - generalization: there exists a deterministic stationary Markov policy π_U → the policy follows coverRule U o, for a cover U of size exactly K and an assignment o, and coverRule is deterministic; reason: this is the policy of the source's proof, and it implies the existence claim
--   - encoding: fresh randomization → one Exp(1) coin per event, in a private coordinate of the seed space; reason: any randomization over the countable decision set is a measurable function of it
--   - encoding: independent Poisson streams, one per type; nonanticipating decisions on the observed history and internal randomization → one marked Poisson stream of rate Λ, the published admissible filtration, which also shows the virtual departure times of agents already matched; reason: same law for the arrivals; those extra times are independent of the future, so they act as private randomization
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Proposition C.3, (44), p.29

import Definitions.Def_ImpatientMatching_Construction

open scoped ENNReal
open NSWApxHard.Reduction DynStochMatching.Reward

namespace ImpatientMatching

/-- **Proposition C.3 (reward from a small cover).** Yan–Varma, manuscript (sha256 7b1051b6…), (44), p.29: if `τ(H) ≤ K`, there is a deterministic
stationary Markov policy `π_U` on the Finite-Zero construction with `g^{π_U} ≥ Γ − 4m/L − εn/32`.

**Formalization Note.** The conclusion names the source's policy: `π_U` follows `coverRule U o` for a
cover `U` of size exactly `K` and an assignment `o`. -/
theorem proposition_C_3 (H : GraphInput) (K : ℕ) (hH : IsSourceRange H K) (hn : n0FZ ≤ H.N)
    (hYes : tau H ≤ K) :
    ∃ (U : Finset (Fin H.N)) (o : Fin (edgeCount H) → Fin H.N) (π : MatchingPolicy),
      U.card = K ∧ IsCoverAssignment H U o ∧ IsDeterministicRule (coverRule U o) ∧
      Realizes (fzInstance H K) (coverRule U o) π ∧
      (((Gamma LFZ H K : ℝ) - 4 * (edgeCount H : ℝ) / (LFZ : ℝ) - (eps : ℝ) * (H.N : ℝ) / 32 :
        ℝ) : EReal) ≤ averageReward (fzInstance H K) π := by sorry

end ImpatientMatching
