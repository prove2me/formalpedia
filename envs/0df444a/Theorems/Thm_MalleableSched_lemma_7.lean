-- Prove2me | Theorems.Thm_MalleableSched_lemma_7
-- name    : MalleableSched.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:00.644108+00:00
-- url     : https://prove2.me/theorems/d790909c-6c27-45e6-a4a3-b2bdd84530e6
-- title:
--   Lemma 7 — Type 1 load: $\sum_{j\in J^1_i}f_j(\{i\})\le2\ell_i\le2C$ (display (1))
-- statement:
--   Throughout, as in §2.1: every speed function $g_j$ is nonnegative and fractionally subadditive, $\mathbf S$ is an assignment, $C=L(\mathbf S)$ is finite, and $\Delta\in\mathbb R^{M\times J}$ satisfies both conditions of Lemma 4: $\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ and $\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j$ and $T\subseteq S_j$.
--
--   Let $x'$ be a feasible solution of (LP1) and fix an orientation of $G(x')$ with every in-degree at most $1$. For a machine $i$ let $J^1_i=\{j\in J:i_j=i,\ x'_{i_jj}>1/2\}$ and $\ell_i=\sum_{j'\in J^1_i}\frac1{\Delta_{ij'}}x'_{ij'}$. Then
--   $$
--   \sum_{j\in J^1_i}f_j(\{i\})\le2\ell_i\le2C .
--   $$
--
--   So the Type 1 jobs load each machine by at most $2C$; the intermediate bound $2\ell_i$ is what Lemma 9 uses.
--
--   Differences from the source:
--   - generalization: Σ_{j∈J¹ᵢ} fⱼ({i}) ≤ 2C (Lemma 7) → Σ_{j∈J¹ᵢ} fⱼ({i}) ≤ 2ℓᵢ and ℓᵢ ≤ C (display (1)); reason: display (1) is what the proof of Lemma 7 shows (p.29) and it implies the printed bound
--   - generalization: x′ an extreme point solution of (LP1) → x any feasible solution of (LP1); reason: the proof uses only feasibility of x′ and the in-degree property of the orientation; extreme points are feasible
--   - encoding: J¹ᵢ = {j : iⱼ = i, x′_{iⱼ j} > 1/2} → the jobs j with (i, j) a support edge directed i → j and x i j > 1/2; reason: under in-degree at most 1 that in-edge is the unique iⱼ
--   - encoding: an orientation of G(x′) in which every node has in-degree at most 1 → toJob : Fin m → Fin n → Prop (edge (i, j) directed i → j iff toJob i j) with InDegLeOne (supportEdges x) toJob; reason: each edge of the bipartite support graph gets one direction; values off the edge set are irrelevant
--   - encoding: C := L(S) → a real C with 0 ≤ C and maxLoad g S = ENNReal.ofReal C; reason: (LP1) needs C to be a real number; this excludes only L(S) = ∞, where Theorem 1 holds for every S′
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Lemma 7, p.9, in the form of Appendix B.3, display (1), p.29

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_LP1
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

open scoped ENNReal

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **Lemma 7 (Type 1 load), in the form of display (1).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Lemma 7, p.9: "For i ∈ M let J1_i := {j ∈ J : ij = i, x′_{ij j} > 1/2}. Then
Σ_{j∈J1_i} fj({i}) ≤ 2C." Appendix B.3, display (1), p.29: "Recall that in the proof of
Lemma 7, we showed that Σ_{j∈J1_i} fj({i}) ≤ 2ℓi ≤ 2C. (1)"

**Formalization Note.** Standing context of §2.1 (p.8): every `g j` is nonnegative and fractionally subadditive, `S` is an
assignment, `C := L(S)` (here a real `C ≥ 0` with `maxLoad g S = ENNReal.ofReal C`), and `Δ`
satisfies both constraints of Lemma 4.
`x` is any feasible solution of (LP1) (the proof uses only feasibility, not extremality) and
`toJob` an orientation of its support graph with in-degree at most one. The conclusion is display
(1): `Σ_{j ∈ J¹ᵢ} fⱼ({i}) ≤ 2ℓᵢ` and `ℓᵢ ≤ C`, which together give the printed `≤ 2C`. -/
theorem lemma_7 {n m : ℕ}
    (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S)
    (C : ℝ) (hC : 0 ≤ C) (hL : maxLoad g S = ENNReal.ofReal C)
    (Δ : Matrix (Fin m) (Fin n) ℝ)
    (hΔ1 : ∀ j, ∑ i ∈ S j, Δ i j = g j (S j))
    (hΔ2 : ∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : LP1Feasible Δ S C x)
    (toJob : Fin m → Fin n → Prop) (hor : InDegLeOne (supportEdges x) toJob) (i : Fin m) :
    (∑ j ∈ J1 x toJob i, procTime g j {i}) ≤ ENNReal.ofReal (2 * ell Δ x toJob i) ∧
      ell Δ x toJob i ≤ C := by sorry

end MalleableSched
