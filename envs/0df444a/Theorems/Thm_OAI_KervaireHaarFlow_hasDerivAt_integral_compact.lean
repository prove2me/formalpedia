-- Prove2me | Theorems.Thm_OAI_KervaireHaarFlow_hasDerivAt_integral_compact
-- name    : OAI.KervaireHaarFlow.hasDerivAt_integral_compact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:21:57.542519+00:00
-- url     : https://prove2.me/theorems/a5365878-f03d-4c57-a022-285c03f02549
-- title:
--   Differentiating under the integral over a compact space
-- statement:
--   Let $S$ be a compact second-countable space with a finite Borel measure $\mu$. Let $f,df:\mathbb R\times S\to E$ be jointly continuous, with $df(t,x)$ the derivative of $u\mapsto f(u,x)$ at $t$ for every $x$. Then $u\mapsto\int f(u,x)\,d\mu(x)$ is differentiable, with derivative
--   $$
--   \int df(t,x)\,d\mu(x)
--   $$
--   at every $t$.
--
--   No integrability assumptions beyond continuity are needed, thanks to compactness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean#L35-L55

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

open OAI OAI.KervaireHaarFlow
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
variable {S E : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S]
  [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} [IsFiniteMeasure μ]

theorem OAI.KervaireHaarFlow.hasDerivAt_integral_compact {f df : ℝ → S → E}
    (hf : Continuous (Function.uncurry f)) (hd : Continuous (Function.uncurry df))
    (hfd : ∀ t x, HasDerivAt (fun u ↦ f u x) (df t x) t) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ x, f u x ∂μ) (∫ x, df t x ∂μ) t := by sorry
