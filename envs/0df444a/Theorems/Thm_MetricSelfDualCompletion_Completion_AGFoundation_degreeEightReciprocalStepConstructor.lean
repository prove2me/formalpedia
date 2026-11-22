-- Prove2me | Theorems.Thm_MetricSelfDualCompletion_Completion_AGFoundation_degreeEightReciprocalStepConstructor
-- name    : MetricSelfDualCompletion.Completion.AGFoundation.degreeEightReciprocalStepConstructor
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T14:57:12.69639+00:00
-- url     : https://prove2.me/theorems/d36f6e62-0387-4548-9bbd-0746351899b9
-- title:
--   Eisenstein, irreducible and separable degree-eight source step
-- statement:
--   For a normalized place $P$ of $K$ and $x$ with $\operatorname{ord}_P(x)=-1$, put $t=(x^8/(x^7+1))^{-1}$ in the actual valuation ring $V_P$. The ring $V_P$ is a discrete valuation ring, and $Y^8+tY^7+t$ is monic, of degree eight, and Eisenstein at its maximal ideal. Its coefficient image in $K[Y]$ is monic, of degree eight, irreducible and separable. The conclusion holds in every characteristic: the derivative coefficients $8$ and $7t$ cannot both vanish.
-- source:
--   Degree-eight reciprocal Garcia–Stichtenoth source recursion from the Shpilka–Guruswami appendix used in STOC 2027 paper 5; Mathlib Eisenstein criterion and irreducibility under the fraction-field coefficient map, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_MetricSelfDualCompletion_AG_SourceStepPolynomialData
set_option autoImplicit false
open MetricSelfDualCompletion.Completion.AGFoundation

theorem MetricSelfDualCompletion.Completion.AGFoundation.degreeEightReciprocalStepConstructor
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsDiscreteValuationRing P.valuationRing ∧
      (StepData.integralPolynomial P x hx).Monic ∧
      (StepData.integralPolynomial P x hx).natDegree = 8 ∧
      (StepData.integralPolynomial P x hx).IsEisensteinAt
        (IsLocalRing.maximalIdeal P.valuationRing) ∧
      (StepData.polynomial P x hx).Monic ∧
      (StepData.polynomial P x hx).natDegree = 8 ∧
      Irreducible (StepData.polynomial P x hx) ∧
      (StepData.polynomial P x hx).Separable := by sorry
