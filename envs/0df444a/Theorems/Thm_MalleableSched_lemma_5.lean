-- Prove2me | Theorems.Thm_MalleableSched_lemma_5
-- name    : MalleableSched.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:51.292412+00:00
-- url     : https://prove2.me/theorems/dfe468a3-d902-4421-94f7-681cf0128e81
-- title:
--   Lemma 5 — (LP1) has a feasible solution
-- statement:
--   Throughout, as in §2.1: every speed function $g_j$ is nonnegative and fractionally subadditive, $\mathbf S$ is an assignment, $C=L(\mathbf S)$ is finite, and $\Delta\in\mathbb R^{M\times J}$ satisfies both conditions of Lemma 4: $\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ and $\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j$ and $T\subseteq S_j$.
--
--   Then the LP (LP1) built from $\Delta$ and $C$,
--   $$
--   \sum_{i\in S_j^+}x_{ij}\ge1\ \ (j\in J),\qquad \sum_{j\in J:\,i\in S_j^+}\frac{1}{\Delta_{ij}}x_{ij}\le C\ \ (i\in M),\qquad x\ge0,
--   $$
--   with $S_j^+=\{i\in S_j:\Delta_{ij}>0\}$, has a feasible solution.
--
--   Feasibility gives the extreme point $x'$ that the proof of Theorem 1 rounds.
--
--   Differences from the source:
--   - encoding: C := L(S) → a real C with 0 ≤ C and maxLoad g S = ENNReal.ofReal C; reason: (LP1) needs C to be a real number; this excludes only L(S) = ∞, where Theorem 1 holds for every S′
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Lemma 5, p.8

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_LP1

namespace MalleableSched

/-- **Lemma 5 ((LP1) is feasible).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Lemma 5, p.8: "(LP1) has a feasible solution."

**Formalization Note.** Standing context of §2.1 (p.8): every `g j` is nonnegative and fractionally subadditive, `S` is an
assignment, `C := L(S)` (here a real `C ≥ 0` with `maxLoad g S = ENNReal.ofReal C`), and `Δ`
satisfies both constraints of Lemma 4.
The exclusion `L(S) = ∞` is where the paper's `C` is not a real number; Theorem 1 is trivial
there. -/
theorem lemma_5 {n m : ℕ}
    (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S)
    (C : ℝ) (hC : 0 ≤ C) (hL : maxLoad g S = ENNReal.ofReal C)
    (Δ : Matrix (Fin m) (Fin n) ℝ)
    (hΔ1 : ∀ j, ∑ i ∈ S j, Δ i j = g j (S j))
    (hΔ2 : ∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T) :
    ∃ x : Matrix (Fin m) (Fin n) ℝ, LP1Feasible Δ S C x := by sorry

end MalleableSched
