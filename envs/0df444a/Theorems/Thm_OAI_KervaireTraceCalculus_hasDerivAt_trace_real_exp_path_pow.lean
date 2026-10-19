-- Prove2me | Theorems.Thm_OAI_KervaireTraceCalculus_hasDerivAt_trace_real_exp_path_pow
-- name    : OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:44:17.747443+00:00
-- url     : https://prove2.me/theorems/b40ae2fd-e691-4ed9-a972-14d33bcc9d78
-- title:
--   Derivative of traced powers along an exponential path
-- statement:
--   Let $\tau$ be a continuous linear functional on a normed algebra that is tracial: $\tau(ab)=\tau(ba)$. For elements $U,C$ and $n\in\mathbb N$, the function $y\mapsto\tau\bigl((Ue^{yC})^n\bigr)$ is differentiable at every $t$, with derivative
--   $$
--   n\,\tau\bigl((Ue^{tC})^nC\bigr).
--   $$
--
--   It is the basic derivative used to differentiate trace logarithms along unitary paths $Ue^{tC}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/TraceCalculus.lean#L110-L128

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

theorem OAI.KervaireTraceCalculus.hasDerivAt_trace_real_exp_path_pow (τ : A →L[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (U C : A) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => τ ((U * NormedSpace.exp (y • C)) ^ n))
      ((n : ℂ) * τ ((U * NormedSpace.exp (t • C)) ^ n * C)) t := by sorry
