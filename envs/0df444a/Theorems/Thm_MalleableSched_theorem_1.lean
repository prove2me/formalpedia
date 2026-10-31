-- Prove2me | Theorems.Thm_MalleableSched_theorem_1
-- name    : MalleableSched.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:53.524751+00:00
-- url     : https://prove2.me/theorems/3d89163d-9085-41c1-8634-56a9a3a83692
-- title:
--   Theorem 1 — fractionally subadditive speeds: every assignment has a well-structured one with $L(\mathbf S')\le\frac{2e}{e-1}L(\mathbf S)$
-- statement:
--   Let $J$ be a finite set of jobs and $M$ a finite set of machines, and let every job $j$ have a fractionally subadditive speed function $g_j:2^M\to\mathbb R_{\ge0}$, with processing times $f_j(S)=1/g_j(S)$. For every assignment $\mathbf S$ there is a well-structured assignment $\mathbf S'$ with
--   $$
--   L(\mathbf S')\le\frac{2e}{e-1}\,L(\mathbf S).
--   $$
--
--   Since a well-structured assignment can be turned into a schedule whose makespan equals its maximum load, the optimal makespan of malleable scheduling with fractionally subadditive speeds is within the factor $\frac{2e}{e-1}\approx3.16$ of the optimal maximum load. No monotonicity of the speeds is assumed.
--
--   **Formalization Note** If $L(\mathbf S)=\infty$ the bound holds for every $\mathbf S'$, as in the paper.
--
--   Differences from the source:
--   - generalization: processing times fⱼ : 2^M → ℝ≥0 finite on non-empty sets (p.2), i.e. gⱼ(S) > 0 for S ≠ ∅ → only gⱼ(S) ≥ 0; speed 0 gives processing time ∞ in ℝ≥0∞; reason: the paper itself uses fⱼ(∅) = ∞ and infinite processing times (p.3, Appendix A.1); instances with positive speeds are a special case
--   - encoding: fⱼ(S) = 1/gⱼ(S), with 1/0 = ∞; loads and L(S) = max over machines → procTime = (ENNReal.ofReal (g j S))⁻¹ in ℝ≥0∞; maxLoad = ⨆ over machines of the summed times; reason: ℝ≥0∞ has 0⁻¹ = ⊤, matching fⱼ(∅) = ∞; a finite ⨆ is the maximum
--   - encoding: 2e/(e−1) → 2 * Real.exp 1 / (Real.exp 1 - 1), cast with ENNReal.ofReal; reason: the same real number
--   - encoding: job set J and machine set M; set functions on 2^M → Fin n and Fin m (0-based); Finset (Fin m); reason: Lean convention; any finite sets relabel to these
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Theorem 1, p.7

import Mathlib
import Definitions.Def_MalleableSched_Model

open scoped ENNReal

namespace MalleableSched

/-- **Theorem 1 (fractionally subadditive speeds: any assignment is well-structured within a
factor 2e/(e−1)).**
Fotakis, Matuschke & Papadigenopoulos, *Assigning and Scheduling Generalized Malleable Jobs
under Subadditive or Submodular Processing Speeds*, arXiv:2111.06225v2, Theorem 1, p.7: "Assume that all processing speed functions are fractionally
subadditive. For any assignment S, there exists a well-structured assignment S′ with
L(S′) ≤ 2e/(e−1) L(S)."

**Formalization Note.** Jobs `Fin n`, machines `Fin m`; speeds `g j S ≥ 0` are real, and
processing times `fⱼ(S) = 1/gⱼ(S)` and loads are in `ℝ≥0∞` (speed `0` means time `∞`).
`L` is `maxLoad`, the maximum over machines of the summed processing times. The constant
`2e/(e−1)` is `2 * Real.exp 1 / (Real.exp 1 - 1)`. No monotonicity of the speeds is assumed, and
none is needed (p.4). If `L(S) = ∞` the bound holds for every `S′`. -/
theorem theorem_1 {n m : ℕ} (g : Fin n → Finset (Fin m) → ℝ) (hg0 : ∀ j S, 0 ≤ g j S)
    (hFS : ∀ j, FractionallySubadditive (g j))
    (S : Fin n → Finset (Fin m)) (hS : IsAssignment S) :
    ∃ S' : Fin n → Finset (Fin m), IsAssignment S' ∧ WellStructured S' ∧
      maxLoad g S' ≤ ENNReal.ofReal (2 * Real.exp 1 / (Real.exp 1 - 1)) * maxLoad g S := by sorry

end MalleableSched
