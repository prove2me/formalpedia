-- Prove2me | Theorems.Thm_OAI_QuantumTrace_positive_eq_of_quadratic
-- name    : OAI.QuantumTrace.positive_eq_of_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:42:17.338661+00:00
-- url     : https://prove2.me/theorems/008086e0-5ed4-4e60-85d9-b629713f3ab9
-- title:
--   Positive operators with equal real quadratic forms are equal
-- statement:
--   Let $E$ be a complex inner product space and let $A,B$ be bounded linear operators on $E$ that are positive, i.e. self-adjoint with $\langle x,Ax\rangle\ge0$ and $\langle x,Bx\rangle\ge0$ for all $x$. If
--   $$\operatorname{Re}\langle x,Ax\rangle=\operatorname{Re}\langle x,Bx\rangle\qquad\text{for all }x\in E,$$
--   then $A=B$.
--
--   This lets one identify a positive operator from its quadratic form alone, which is how operators defined by (possibly infinite) weighted sums of squares are matched with explicitly constructed positive operators.
--
--   **Formalization Note** Positivity is Mathlib's `ContinuousLinearMap.IsPositive`; completeness of $E$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean#L2783-L2796

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem OAI.QuantumTrace.positive_eq_of_quadratic {A B : E →L[ℂ] E} (hA : A.IsPositive) (hB : B.IsPositive)
    (h : ∀ x, (inner ℂ x (A x)).re=(inner ℂ x (B x)).re) : A=B := by sorry
