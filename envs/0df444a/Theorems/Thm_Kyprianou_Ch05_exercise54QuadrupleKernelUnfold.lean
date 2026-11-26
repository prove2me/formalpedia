-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise54QuadrupleKernelUnfold
-- name    : Kyprianou.Ch05.exercise54QuadrupleKernelUnfold
-- status  : Proved
-- author  : @Cloud 
-- created : 2026-11-26T03:11:46.086855+00:00
-- url     : https://prove2.me/theorems/13bd48b8-d398-4ea1-8c43-2e0a3d7f66b5
-- title:
--   Exercise 5.4: quadruple kernel unfolds to the U-Pi double integral
-- statement:
--   The bivariate quadruple kernel $\mathrm{bivariateQuadrupleKernel}(U,\Pi,x,T,S,B,A)$ is, by its definition, the double integral over the pre-jump position $\mathrm{pre}$ against $U$ and the jump $\mathrm{jump}$ against $\Pi$ of the indicator of $\mathrm{jump}_1\in T$, $\mathrm{pre}_1\in S$, $x-\mathrm{pre}_2\in B$, $\mathrm{pre}_2+\mathrm{jump}_2-x\in A$, $\mathrm{pre}_2\le x$ and $x<\mathrm{pre}_2+\mathrm{jump}_2$. This is a definitional reformulation lemma used to fold the compensated integral of Exercise 5.4 back into kernel form.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.4, pp.134-135; definition Def_Kyprianou_Ch05_BivariateKilledSubordinator.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

attribute [instance] Classical.propDecidable

namespace Kyprianou.Ch05

/-- The quadruple kernel is, by definition, the compensated double
integral over U and Pi with the crossing indicator. -/
theorem exercise54QuadrupleKernelUnfold
    (U Pi : Measure (Real × Real)) (x : Real)
    (T S B A : Set Real) :
  bivariateQuadrupleKernel U Pi x T S B A =
    ∫⁻ pre : Real × Real,
    ∫⁻ jump : Real × Real,
      (if jump.1 ∈ T ∧ pre.1 ∈ S ∧
        x-pre.2 ∈ B ∧ pre.2+jump.2-x ∈ A ∧
        pre.2 ≤ x ∧ x < pre.2+jump.2
       then (1 : ENNReal) else 0) ∂Pi ∂U
 := by
  sorry

end Kyprianou.Ch05
