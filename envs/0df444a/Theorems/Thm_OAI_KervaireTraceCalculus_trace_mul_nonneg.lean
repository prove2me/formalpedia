-- Prove2me | Theorems.Thm_OAI_KervaireTraceCalculus_trace_mul_nonneg
-- name    : OAI.KervaireTraceCalculus.trace_mul_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:43:18.576059+00:00
-- url     : https://prove2.me/theorems/4c81a1ef-b204-4c73-aa09-3c0c47ccfb59
-- title:
--   Positivity of the trace of a product of positives
-- statement:
--   Let $\tau$ be a tracial continuous functional on a C*-algebra with $\mathrm{Re}\,\tau(X^*X)\ge0$ for all $X$. For positive elements $B,D$,
--   $$
--   \mathrm{Re}\,\tau(DB)\ge0 .
--   $$
--
--   Positivity of a trace extends from squares to products of two positive elements.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean#L72-L91

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

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
attribute [local instance] OAI.KervaireTraceCalculus.instContinuousFunctionalCalculusRealIsSelfAdjoint_oAI
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

theorem OAI.KervaireTraceCalculus.trace_mul_nonneg (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B D : A} (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ (τ (D * B)).re := by sorry
