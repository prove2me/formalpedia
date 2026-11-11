-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_6_2
-- name    : MatchIndiff.PublicSM.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:31.371198+00:00
-- url     : https://prove2.me/theorems/e5d7057b-542b-400e-b768-071b92e0db07
-- title:
--   Lemma 6.2 — Algorithm 1's base market has exactly k² + k stable matchings
-- statement:
--   For every even $k\ge2$, the trace $M_0,\dots,M_L$ of Algorithm 1 on $3k$ students and $3k$ schools has no repeated student–school visit, and consecutive steps share students. Consequently, with its chronological student lists and fixed strict complete reverse-chronological school priorities, the market has exactly
--   $$L+1=k^2+k$$
--   stable matchings.
--
--   **Formalization Note.** The trace is `algTrace k`, `algL k` $=k^2+k-1$; the count is the `Set.ncard` of the stable set.
--
--   Differences from the source:
--   - generalization: Q_k: reverse chronological order of holders, then all other students in one fixed strict order → every strict complete Q satisfying IsRevChronPriority for the trace; reason: the paper leaves the order of the non-holders unspecified; every choice is covered, so the statement specializes to Q_k
--   - reading: stable matchings of the strict market → for each α ∈ {weak, strong, super}, the α-stable set; reason: the notions coincide on strict profiles
--   - encoding: students A_i, B_i, C_j and schools a_i, b_i, c_j, 1-based → Fin (3k) with A_i = i, B_i = k + i, C_j = 2k + j (0-based i, j), same for schools; reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 11, Lemma 6.2

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Trace

namespace MatchIndiff.PublicSM

/-- Lemma 6.2 (p. 11): the trace of Algorithm 1 has no repeated student–school visit and
consecutive steps share students; with its chronological student lists and any strict complete
reverse-chronological school priorities, the market has exactly `L + 1 = k² + k` stable
matchings. -/
theorem lemma_6_2 (k : ℕ) (hk : 2 ≤ k) (hev : Even k) :
    NoRevisit (algTrace k) (algL k) ∧ ConsecShare (algTrace k) (algL k) ∧
      algL k + 1 = k ^ 2 + k ∧
      ∀ Q : Fin (3 * k) → Fin (3 * k) → ℕ, IsRevChronPriority (algTrace k) (algL k) Q →
        ∀ α : StabKind,
          {μ : Matching (3 * k) (3 * k) | IsStable α (chronRow (algTrace k) (algL k)) Q μ}.ncard =
            k ^ 2 + k := by sorry

end MatchIndiff.PublicSM
