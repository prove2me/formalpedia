-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_Quantum_Submeasurement_total_le_one
-- name    : LIDT.MIPStarRE.Quantum.Submeasurement.total_le_one
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:16:57.579989+00:00
-- url     : https://prove2.me/theorems/e382ceb2-81d6-4534-a11b-1b0b770dd266
-- title:
--   Total Le One
-- statement:
--   **The total operator of a submeasurement is bounded by the identity.**
--
--   For every finite-outcome submeasurement `M`, the sum of all outcome effects is below the identity in operator order:
--
--   $$
--   M.\operatorname{total}\le1.
--   $$
--
--   This is the named-total restatement of the underlying outcome-sum bound. It is the basic positivity and contraction fact used whenever a submeasurement total appears as the middle operator in a sandwich estimate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.Quantum.Submeasurement.total_le_one`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/Measurement.lean#L82-L85

import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib

open LIDT
/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed submeasurements via answer relabeling.
* `Measurement.postprocess` — the paper's postprocessing proposition for complete POVMs.
* `inconsistency` — the off-diagonal mass `∑_{a ≠ b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## References

This file builds the project's finite-dimensional measurement layer on top of
the normalized-trace and positive-operator facts in `MIPStarRE.Quantum.FiniteMatrix`
for the quantum formalization in `references/ldt-paper/`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.Quantum

/-! ## Submeasurements and measurements -/





/-! ## Totals and postprocessing -/

open LIDT.MIPStarRE.Quantum.Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

theorem LIDT.MIPStarRE.Quantum.Submeasurement.total_le_one (M : _root_.LIDT.MIPStarRE.Quantum.Submeasurement α d) :
    M.total ≤ 1 := by sorry
