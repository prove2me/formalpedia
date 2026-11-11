-- Prove2me | Theorems.Thm_MatchIndiff_PublicSM_lemma_6_3
-- name    : MatchIndiff.PublicSM.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:26:42.242802+00:00
-- url     : https://prove2.me/theorems/4b310797-751d-42f0-a729-ab3b49e732e3
-- title:
--   Lemma 6.3 — the strong (= super) stable set at the marked profile P^{X,Y}
-- statement:
--   Fix an even $k\ge2$, Algorithm 1's trace, a strict complete reverse-chronological priority profile $Q_k$, and bit arrays $X,Y\in\{0,1\}^I$. For either strong or super stability, the entire stable set at $(P^{X,Y},Q_k)$ is
--   $$\{M_L\}\cup\{M_{t(i,j)}:\ (i,j)\in I,\ X_{ij}=Y_{ij}=0\}.$$
--   In particular every profile has a stable matching. If any controlled position survives, the student rank vector of $M_L$ is not optimal: in every public student order some stable matching has a lexicographically smaller rank vector.
--
--   The fooling-set argument of Theorem 6.2 rests on this: complementary arrays leave only $M_L$, while a mixed array with $X_{ij}=Y_{ij}=0$ revives $M_{t(i,j)}$.
--
--   Differences from the source:
--   - generalization: Q_k: reverse chronological order of holders, then all other students in one fixed strict order → every strict complete Q satisfying IsRevChronPriority for the trace; reason: the paper leaves the order of the non-holders unspecified; every choice is covered, so the statement specializes to Q_k
--   - reading: the student rank vector of M_L is not optimal → for every public student order ρ some α-stable ν has rankVec ρ ν lexicographically smaller than rankVec ρ M_L; reason: the selector compares rank vectors lexicographically in the public order; the proof (p. 79) gives this for every order
--   - encoding: (i, j) ∈ I with 1 ≤ i ≤ k, 1 ≤ j < k, positions t(i, j) = (i − 1)(k + 1) + j → i : Fin k, j : Fin (k − 1) (0-based), position coreStep k i j = i(k + 1) + j + 1, X i j = false for X_{ij} = 0; reason: Lean convention, same set
--   - encoding: α ∈ {strong, super} → α : StabKind with α ≠ weak; reason: Lean convention
-- source:
--   Zhang, Zhao, Xu, Xi, Zhao, Structural Complexity of Matching with Indifferences, STOC 2027 submission (manuscript sha256 22dfb437…), p. 12, Lemma 6.3

import Mathlib
import Definitions.Def_MatchIndiff_PublicSM_Model
import Definitions.Def_MatchIndiff_PublicSM_Trace

namespace MatchIndiff.PublicSM

/-- Lemma 6.3 (p. 12): for strong or super stability, the stable set at `(P^{X,Y}, Q_k)` is
`{M_L} ∪ {M_{t(i,j)} : X_{ij} = Y_{ij} = 0}`; every profile has a stable matching; and if a
controlled position survives, some stable matching has a lexicographically smaller student rank
vector than `M_L` in every public student order. -/
theorem lemma_6_3 (k : ℕ) (hk : 2 ≤ k) (hev : Even k) (Q : Fin (3 * k) → Fin (3 * k) → ℕ)
    (hQ : IsRevChronPriority (algTrace k) (algL k) Q) (X Y : Fin k → Fin (k - 1) → Bool)
    (α : StabKind) (hα : α ≠ StabKind.weak) :
    (∀ μ : Matching (3 * k) (3 * k), IsStable α (markedProfile k X Y) Q μ ↔
        ((∀ s, μ.toFun s = some (algTrace k (algL k) s)) ∨
          ∃ (i : Fin k) (j : Fin (k - 1)), X i j = false ∧ Y i j = false ∧
            ∀ s, μ.toFun s = some (algTrace k (coreStep k i.val j.val) s))) ∧
      (∃ μ : Matching (3 * k) (3 * k), IsStable α (markedProfile k X Y) Q μ) ∧
      ((∃ (i : Fin k) (j : Fin (k - 1)), X i j = false ∧ Y i j = false) →
        ∀ (ρ : Fin (3 * k) ≃ Fin (3 * k)) (μL : Matching (3 * k) (3 * k)),
          (∀ s, μL.toFun s = some (algTrace k (algL k) s)) →
          ∃ ν : Matching (3 * k) (3 * k), IsStable α (markedProfile k X Y) Q ν ∧
            List.Lex (· < ·) (rankVec ρ (markedProfile k X Y) ν) (rankVec ρ (markedProfile k X Y) μL)) := by sorry

end MatchIndiff.PublicSM
