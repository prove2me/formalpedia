-- Prove2me | Theorems.Thm_MWCSherali_theorem_4_1
-- name    : MWCSherali.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:06.569518+00:00
-- url     : https://prove2.me/theorems/a9a6262b-32c8-4ddf-9890-7812a333daf3
-- title:
--   Theorem 4.1 — a $k=4$ solution of the continuous Flow LP of value at most $2.54492029$
-- statement:
--   There is a feasible solution $(F_{a,i},B_i)$ of (Continuous-Flow-LP) for $k=4$ with
--
--   $$\sum_{i=1}^4B_i(\Delta_4)\le2.54492029 .$$
--
--   Hence $Q_4\le2.54492029$; with Theorems 3.2 and 3.4 and Lemma 2.5 this gives UG-hardness of Multiway Cut within $8/(4+2.54492029)>1.22232$.
--
--   Differences from the source:
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: Borel measures on Δ_k, probability measures on Γ_a → measures on Fin k → ℝ giving the complement of Δ_k (resp. Γ_a) measure 0; reason: Lean convention; the same measures
--   - encoding: nonnegative capacity measures B_i → B_i required to be finite measures; reason: an infinite capacity has objective ∞ and changes no infimum; it makes every integral a genuine one
--   - encoding: a feasible solution (F_{a,i}, B_i) → a triple (F, B, ν) with ContFlowFeasible 4 F B ν; reason: the exit measures ν_a are variables of the program (p.27)
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 4.1, p.31

import Mathlib
import Definitions.Def_MWCSherali_ContFlowFeasible

namespace MWCSherali

open MeasureTheory

/-- **Theorem 4.1 (a `k = 4` solution of the continuous Flow LP).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 4.1,
p.31: "There exists a feasible solution `(F_{a,i}, B_i)` to (Continuous-Flow-LP) when `k = 4` such
that `∑_{i=1}^4 B_i(Δ₄) ≤ 2.54492029`."

**Formalization Note.** A feasible solution includes the exit measures `ν_a` (p.27: they are
variables of the program, "determined by `F_{a,i}` and the LP constraints"). The bound is in
`ℝ≥0∞`, where `B_i(Δ₄)` lives. -/
theorem theorem_4_1 :
    ∃ (F : Fin 4 → Fin 4 → Measure (Fin 4 → ℝ)) (B : Fin 4 → Measure (Fin 4 → ℝ))
      (ν : Fin 4 → Measure (Fin 4 → ℝ)), ContFlowFeasible 4 F B ν ∧
        ∑ i, B i (stdSimplex ℝ (Fin 4)) ≤ ENNReal.ofReal 2.54492029 := by sorry

end MWCSherali
