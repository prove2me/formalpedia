-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_tendsto_smoothTrace_vectorCLM
-- name    : OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:49:48.967067+00:00
-- url     : https://prove2.me/theorems/17504d7d-9d4b-48e1-816b-a52871c66505
-- title:
--   Smooth traced phases converge to the vector phase
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, let $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ be its fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ the spectral measure of $\xi$. Along the cut approach $a_n=(1-\varepsilon_n^2)+\varepsilon_ni$ with $\varepsilon_n=1/(n+2)$, the smooth traced phases of the vector functional converge:
--   $$
--   \int\mathrm{ph}_{a_n}\,d\mu_\xi\ \to\ \mathrm{ph}_\xi(U).
--   $$
--
--   This is how inequalities for the smooth regularization pass to the fractional phase.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralApproximation.lean#L131-L155

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

theorem OAI.KervaireSpectral.tendsto_smoothTrace_vectorCLM (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorCLM ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (vectorPhase U ξ)) := by sorry
