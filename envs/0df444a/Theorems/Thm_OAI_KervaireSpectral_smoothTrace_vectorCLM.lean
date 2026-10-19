-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_smoothTrace_vectorCLM
-- name    : OAI.KervaireSpectral.smoothTrace_vectorCLM
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:49:07.384424+00:00
-- url     : https://prove2.me/theorems/2b3b2147-70ad-4d00-b735-8ae82a11c882
-- title:
--   Smooth traced phase of a vector functional
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, let $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ be its fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ the spectral measure of $\xi$. For $|a|<1$ let $\mathrm{ph}_a(z)=\frac12+\arg(1-az)/\pi$. Then the smooth traced phase for the functional $T\mapsto\langle\xi,T\xi\rangle$ is
--   $$
--   \frac{\|\xi\|^2}2-\frac1\pi\,\mathrm{Im}\bigl\langle\xi,-\log(1-aU)\xi\bigr\rangle=\int\mathrm{ph}_a(z)\,d\mu_\xi(z).
--   $$
--
--   So the regularized phase of a single vector is an integral of the smooth scalar phase against its spectral measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean#L106-L129

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

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℂ} (ha : ‖a‖ < 1) :
    let _ := isStarNormal_of_mem_unitary hU
    smoothTrace (vectorCLM ξ) a U =
      ∫ z : spectrum ℂ U, smoothPhase a z ∂vectorMeasure U ξ := by sorry
