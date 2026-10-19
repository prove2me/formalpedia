-- Prove2me | Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_trace_pow
-- name    : OAI.KervaireTraceCalculus.hasDerivAt_trace_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:41:37.400679+00:00
-- url     : https://prove2.me/theorems/ee17b53d-dd70-4871-b1f9-bfd55a9e9c1b
-- title:
--   Derivative of the trace of a power
-- statement:
--   Let $\tau$ be a continuous linear functional on a normed algebra that is tracial: $\tau(ab)=\tau(ba)$. If $f$ has derivative $f'$ at $x$, then $y\mapsto\tau(f(y)^n)$ has derivative
--   $$
--   n\,\tau\bigl(f(x)^{n-1}f'\bigr)
--   $$
--   at $x$.
--
--   Under a trace, a power differentiates as if the factors commuted.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean#L23-L40

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
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem OAI.KervaireTraceCalculus.hasDerivAt_trace_pow (τ : E →L[𝕜] F)
    (hτ : ∀ a b : E, τ (a * b) = τ (b * a))
    {f : 𝕜 → E} {f' : E} {x : 𝕜} (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun y => τ (f y ^ n)) (n • τ (f x ^ (n - 1) * f')) x := by sorry
