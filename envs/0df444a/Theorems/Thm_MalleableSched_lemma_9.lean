-- Prove2me | Theorems.Thm_MalleableSched_lemma_9
-- name    : MalleableSched.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:51.370183+00:00
-- url     : https://prove2.me/theorems/9f193b15-ca63-472e-a0aa-4006f652b57b
-- title:
--   Lemma 9 — the reduced assignment $\mathbf T$ is well-structured with $L(\mathbf T)\le\frac{2e}{e-1}L(\mathbf S)$
-- statement:
--   Throughout, as in §2.1: every speed function $g_j$ is nonnegative and fractionally subadditive, $\mathbf S$ is an assignment, $C=L(\mathbf S)$ is finite, and $\Delta\in\mathbb R^{M\times J}$ satisfies both conditions of Lemma 4: $\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ and $\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j$ and $T\subseteq S_j$.
--
--   Let $x'$ be a feasible solution of (LP1) and fix an orientation of $G(x')$ with every in-degree at most $1$. For every Type 2 job $j$ let $\theta^*_j>0$ be a minimizer over $\theta>0$ of
--   $$
--   \max_{i\in T_j(\theta)}2\ell_i+f_j(T_j(\theta)).
--   $$
--   Let $\mathbf T$ be defined by $T_j=T_j(\theta^*_j)$ if $S'_j=\bar S_j$ and $T_j=\{i_j\}$ otherwise. Then $\mathbf T$ is an assignment (every $T_j$ is non-empty), it is well-structured, and
--   $$
--   L(\mathbf T)\le\frac{2e}{e-1}\,L(\mathbf S).
--   $$
--
--   This completes the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: x′ an extreme point solution of (LP1) → x any feasible solution of (LP1); reason: the proof uses only feasibility of x′ and the in-degree property of the orientation; extreme points are feasible
--   - reading: θ*ⱼ a minimizer of max_{i∈Tⱼ(θ)} 2ℓᵢ + fⱼ(Tⱼ(θ)) (p.9), or of 2θ + fⱼ(Tⱼ(θ)) (p.29) → any θstar j > 0 minimizing thresholdObjective (the p.9 function) over θ > 0; reason: the p.29 function need not attain its infimum when some ℓᵢ = 0; the p.9 one takes finitely many values, and the p.29 argument goes through with it
--   - reading: "Let T be the assignment" → IsAssignment T added to the conclusion; reason: the page asserts that T is an assignment, i.e. every Tⱼ is non-empty
--   - encoding: iⱼ, the unique in-neighbour of a Type 1 job → a chosen witness of IsType1 x toJob j; reason: unique under in-degree at most 1
--   - encoding: 2e/(e−1) → 2 * Real.exp 1 / (Real.exp 1 - 1), cast with ENNReal.ofReal; reason: the same real number
--   - encoding: an orientation of G(x′) in which every node has in-degree at most 1 → toJob : Fin m → Fin n → Prop (edge (i, j) directed i → j iff toJob i j) with InDegLeOne (supportEdges x) toJob; reason: each edge of the bipartite support graph gets one direction; values off the edge set are irrelevant
--   - encoding: C := L(S) → a real C with 0 ≤ C and maxLoad g S = ENNReal.ofReal C; reason: (LP1) needs C to be a real number; this excludes only L(S) = ∞, where Theorem 1 holds for every S′
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Lemma 9, p.9 (proof Appendix B.3, pp.28–29)

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_LP1
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

open scoped ENNReal

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **Lemma 9 (the reduced assignment).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Lemma 9, p.9 (proof Appendix B.3, pp.28–29): "Let T be the assignment defined by
Tj = Tj(θ∗) if S′j = S̄j and Tj = {ij} otherwise. Then T is well-structured and
L(T) ≤ 2e/(e−1) L(S)." Here (p.9) "θ∗_j is a minimizer of max_{i∈Tj(θ)} 2ℓi + fj(Tj(θ))" over
θ > 0.

**Formalization Note.** Standing context of §2.1 (p.8): every `g j` is nonnegative and fractionally subadditive, `S` is an
assignment, `C := L(S)` (here a real `C ≥ 0` with `maxLoad g S = ENNReal.ofReal C`), and `Δ`
satisfies both constraints of Lemma 4.
`x` is any feasible solution of (LP1) (extremality is not used), `toJob` an orientation of its
support graph with in-degree at most one, and `θstar j` any minimizer over `θ > 0` of
`thresholdObjective` (the p.9 function) for every Type 2 job `j`. `T = lemma9Assignment`. The
conclusion also records that `T` is an assignment (all `Tⱼ` non-empty), as "the assignment"
on the page asserts. -/
theorem lemma_9 {n m : ℕ}
    (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S)
    (C : ℝ) (hC : 0 ≤ C) (hL : maxLoad g S = ENNReal.ofReal C)
    (Δ : Matrix (Fin m) (Fin n) ℝ)
    (hΔ1 : ∀ j, ∑ i ∈ S j, Δ i j = g j (S j))
    (hΔ2 : ∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : LP1Feasible Δ S C x)
    (toJob : Fin m → Fin n → Prop) (hor : InDegLeOne (supportEdges x) toJob)
    (θstar : Fin n → ℝ)
    (hθ : ∀ j, ¬ IsType1 x toJob j → 0 < θstar j ∧
      ∀ θ : ℝ, 0 < θ → thresholdObjective g Δ x toJob j (θstar j) ≤
        thresholdObjective g Δ x toJob j θ) :
    IsAssignment (lemma9Assignment Δ x toJob θstar) ∧
      WellStructured (lemma9Assignment Δ x toJob θstar) ∧
      maxLoad g (lemma9Assignment Δ x toJob θstar) ≤
        ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1)) * maxLoad g S := by sorry

end MalleableSched
