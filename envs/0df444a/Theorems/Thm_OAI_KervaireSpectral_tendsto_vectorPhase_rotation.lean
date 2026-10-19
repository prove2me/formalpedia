-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_tendsto_vectorPhase_rotation
-- name    : OAI.KervaireSpectral.tendsto_vectorPhase_rotation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:55:22.007173+00:00
-- url     : https://prove2.me/theorems/ba42f44d-1ef1-499a-a38c-45593dd254db
-- title:
--   Phases under small positive rotations
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, let $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ be its fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ the spectral measure of $\xi$. If $a_n\ge0$ and $a_n\to0$, then
--   $$
--   \mathrm{ph}_\xi\bigl(\mathrm{rot}(a_n)U\bigr)\to\mathrm{ph}_\xi(U).
--   $$
--
--   Rotating forward moves eigenvalues away from the cut on the side where the phase is continuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean#L163-L182

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

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.tendsto_vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := fun n => isStarNormal_of_mem_unitary (Unitary.smul_mem
      ⟨scalarRotation (a n), scalarRotation_unitary (a n)⟩ hU)
    Tendsto (fun n => vectorPhase (scalarRotation (a n) • U) ξ) atTop (𝓝 (vectorPhase U ξ)) := by sorry
