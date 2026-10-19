-- Prove2me | Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_traceLog_path
-- name    : OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:44:47.676095+00:00
-- url     : https://prove2.me/theorems/755cdcfa-b503-4756-923e-64c9df6c29cf
-- title:
--   Derivative of the trace logarithm along an exponential path
-- statement:
--   Let $\tau$ be a continuous linear functional on a normed algebra that is tracial: $\tau(ab)=\tau(ba)$. Let $U,C$ be elements with $\|Ue^{tC}\|\le1$ for all $t$, and $|a|<1$. With $\mathrm{TL}(a,V)=\sum_{n\ge0}\frac{a^{n+1}}{n+1}\tau(V^{n+1})$, the function $t\mapsto\mathrm{TL}(a,Ue^{tC})$ is differentiable with derivative
--   $$
--   \sum_{n\ge0}a^{n+1}\,\tau\bigl((Ue^{tC})^{n+1}C\bigr).
--   $$
--
--   This gives the derivative of the regularized traced phase along a path of unitaries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean#L172-L201

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
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem OAI.KervaireTraceCalculus.hasDerivAt_traceLog_path [NormOneClass A] (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A)
    (hb : ∀ t : ℝ, ‖U * NormedSpace.exp (t • C)‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ => traceLog τ a (U * NormedSpace.exp (t • C)))
      (∑' n : ℕ, a ^ (n + 1) * τ ((U * NormedSpace.exp (t • C)) ^ (n + 1) * C)) t := by sorry
