-- Prove2me | Theorems.Thm_MalleableSched_lemma_9_threshold
-- name    : MalleableSched.lemma_9_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:52.803674+00:00
-- url     : https://prove2.me/theorems/0fb6a321-6a68-4a13-9520-2f4117148f9b
-- title:
--   Appendix B.3 — some $\theta>0$ has $2\theta+f_j(T_j(\theta))\le\frac{2e}{e-1}C$
-- statement:
--   Throughout, as in §2.1: every speed function $g_j$ is nonnegative and fractionally subadditive, $\mathbf S$ is an assignment, $C=L(\mathbf S)$ is finite, and $\Delta\in\mathbb R^{M\times J}$ satisfies both conditions of Lemma 4: $\sum_{i\in S_j}\Delta_{ij}=g_j(S_j)$ and $\sum_{i\in T}\Delta_{ij}\le g_j(T)$ for all $j$ and $T\subseteq S_j$.
--
--   Let $x'$ be a feasible solution of (LP1), fix an orientation of $G(x')$ with every in-degree at most $1$, and let $j$ be a job with a Type 2 assignment. With $T_j(\theta)=\{i\in\bar S_j:\ell_i\le\theta\}$ and $\alpha=\frac{2e}{e-1}$, there is some $\theta>0$ with
--   $$
--   2\theta+f_j(T_j(\theta))\le\alpha C .
--   $$
--
--   This is the step of the proof of Lemma 9 that produces the constant $\frac{2e}{e-1}$, the value of $\alpha$ for which $\ln\frac{\alpha}{\alpha-2}=1$.
--
--   Differences from the source:
--   - generalization: x′ an extreme point solution of (LP1) → x any feasible solution of (LP1); reason: the proof uses only feasibility of x′ and the in-degree property of the orientation; extreme points are feasible
--   - encoding: a Type 2 job j (S′ⱼ = S̄ⱼ) → ¬ IsType1 x toJob j; reason: the "otherwise" branch of the construction on p.9
--   - encoding: 2e/(e−1) → 2 * Real.exp 1 / (Real.exp 1 - 1), cast with ENNReal.ofReal; reason: the same real number
--   - encoding: an orientation of G(x′) in which every node has in-degree at most 1 → toJob : Fin m → Fin n → Prop (edge (i, j) directed i → j iff toJob i j) with InDegLeOne (supportEdges x) toJob; reason: each edge of the bipartite support graph gets one direction; values off the edge set are irrelevant
--   - encoding: C := L(S) → a real C with 0 ≤ C and maxLoad g S = ENNReal.ofReal C; reason: (LP1) needs C to be a real number; this excludes only L(S) = ∞, where Theorem 1 holds for every S′
--   - encoding: decision variables xᵢⱼ only for i ∈ S⁺ⱼ → a full m × n real matrix with xᵢⱼ = 0 for i ∉ S⁺ⱼ; reason: an affine copy of the paper's feasible region; feasible points and extreme points correspond
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Appendix B.3, p.29 ("it suffices to show that there exists some θ > 0 such that 2θ + fj(Tj(θ)) ≤ αC")

import Mathlib
import Definitions.Def_MalleableSched_Model
import Definitions.Def_MalleableSched_LP1
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP

open scoped ENNReal

namespace MalleableSched

open UnrelatedSched.TwoApprox

/-- **A good threshold exists (proof of Lemma 9).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Appendix B.3, p.29: "As θ∗_j was chosen to minimize 2θ + fj(Tj(θ)), it suffices to show
that there exists some θ > 0 such that 2θ + fj(Tj(θ)) ≤ αC, for α := 2e/(e−1)."

**Formalization Note.** Standing context of §2.1 (p.8): every `g j` is nonnegative and fractionally subadditive, `S` is an
assignment, `C := L(S)` (here a real `C ≥ 0` with `maxLoad g S = ENNReal.ofReal C`), and `Δ`
satisfies both constraints of Lemma 4.
`x` is any feasible solution of (LP1) (extremality is not used), `toJob` an orientation of its
support graph with in-degree at most one, and `j` a Type 2 job (`¬ IsType1 x toJob j`), the jobs
for which `Tⱼ(θ)` is used. `α = 2e/(e−1)` is `2 * Real.exp 1 / (Real.exp 1 - 1)`. -/
theorem lemma_9_threshold {n m : ℕ}
    (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S)
    (C : ℝ) (hC : 0 ≤ C) (hL : maxLoad g S = ENNReal.ofReal C)
    (Δ : Matrix (Fin m) (Fin n) ℝ)
    (hΔ1 : ∀ j, ∑ i ∈ S j, Δ i j = g j (S j))
    (hΔ2 : ∀ j, ∀ T ⊆ S j, ∑ i ∈ T, Δ i j ≤ g j T)
    (x : Matrix (Fin m) (Fin n) ℝ) (hx : LP1Feasible Δ S C x)
    (toJob : Fin m → Fin n → Prop) (hor : InDegLeOne (supportEdges x) toJob)
    (j : Fin n) (hj : ¬ IsType1 x toJob j) :
    ∃ θ : ℝ, 0 < θ ∧
      ENNReal.ofReal (2 * θ) + procTime g j (thresholdSet Δ x toJob j θ) ≤
        ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1) * C) := by sorry

end MalleableSched
