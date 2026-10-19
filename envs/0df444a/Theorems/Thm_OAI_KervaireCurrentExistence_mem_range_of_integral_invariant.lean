-- Prove2me | Theorems.Thm_OAI_KervaireCurrentExistence_mem_range_of_integral_invariant
-- name    : OAI.KervaireCurrentExistence.mem_range_of_integral_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:40:06.250278+00:00
-- url     : https://prove2.me/theorems/68906581-fe6d-4d22-b9bc-107f72fecc2c
-- title:
--   Equal weighted pushforwards force a common value
-- statement:
--   Let $S$ be a compact space with a finite measure that charges every nonempty open set, and $f_0,f_1:S\to E$ continuous maps to a finite-dimensional space, with continuous weights $j_0,j_1$. Suppose $y=f_0(x)$ for some $x$, that $j_0>0$ at every preimage of $y$ under $f_0$, and that for every smooth compactly supported $\varphi$,
--   $$
--   \int\varphi(f_0)\,j_0\,d\mu=\int\varphi(f_1)\,j_1\,d\mu .
--   $$
--   Then $y$ lies in the range of $f_1$.
--
--   This turns equality of degree-type integrals into surjectivity onto a regular value.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/CurrentExistence.lean#L42-L82

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence

open OAI
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]

theorem OAI.KervaireCurrentExistence.mem_range_of_integral_invariant {f₀ f₁ : S → E} {j₀ j₁ : S → ℝ}
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hj₀ : Continuous j₀)
    (y : E) (hex : ∃ x, f₀ x = y) (hpos : ∀ x, f₀ x = y → 0 < j₀ x)
    (hinv : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ (f₀ x) * j₀ x ∂μ) = ∫ x, φ (f₁ x) * j₁ x ∂μ) :
    y ∈ Set.range f₁ := by sorry
