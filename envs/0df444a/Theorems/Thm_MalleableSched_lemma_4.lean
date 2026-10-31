-- Prove2me | Theorems.Thm_MalleableSched_lemma_4
-- name    : MalleableSched.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:12.650653+00:00
-- url     : https://prove2.me/theorems/70511bd1-8869-4d4b-984d-e1314bec26ff
-- title:
--   Lemma 4 — fractionally subadditive speeds admit core vectors $\Delta$
-- statement:
--   Let every speed function $g_j:2^M\to\mathbb R_{\ge0}$ be fractionally subadditive and let $\mathbf S$ be an assignment. Then there is $\Delta\in\mathbb R^{M\times J}$ such that
--
--   1. $\displaystyle\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ for all $j\in J$;
--   2. $\displaystyle\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j\in J$ and $T\subseteq S_j$.
--
--   For each job, $(\Delta_{ij})_{i\in S_j}$ is a core element of the cost-sharing game with player set $S_j$ and cost function $g_j$. The vectors $\Delta$ are the coefficients of the LP (LP1) used in the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Lemma 4, p.8 (proof p.8 and Appendix B.2, p.28)

import Mathlib
import Definitions.Def_MalleableSched_Model

namespace MalleableSched

/-- **Lemma 4 (core vectors).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Lemma 4, p.8 (proof p.8 and Appendix B.2, p.28): "Assume that gj is fractionally
subadditive for all j ∈ J, let S be an assignment … There exists Δ ∈ R^{M×J} such that
1. Σ_{i∈Sj} Δij = gj(Sj) for all j ∈ J, 2. Σ_{i∈T} Δij ≤ gj(T) for all j ∈ J and T ⊆ Sj."

**Formalization Note.** Speeds are nonnegative reals (`g : 2^M → ℝ≥0`, p.3). `Δ` is a real
`m × n` matrix, rows machines and columns jobs. No sign condition on `Δ` is claimed, as on the
page. -/
theorem lemma_4 {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S) :
    ∃ Δ : Matrix (Fin m) (Fin n) ℝ,
      (∀ j, ∑ i ∈ S j, Δ i j = g j (S j)) ∧
      (∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T) := by sorry

end MalleableSched
