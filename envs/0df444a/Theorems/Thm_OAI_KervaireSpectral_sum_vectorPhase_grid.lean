-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_sum_vectorPhase_grid
-- name    : OAI.KervaireSpectral.sum_vectorPhase_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:56:48.093972+00:00
-- url     : https://prove2.me/theorems/a8ebb7bf-e812-4fce-b898-5c4e0713c4e8
-- title:
--   Phases of grid rotations add up to the phase of a power
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, let $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ be its fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ the spectral measure of $\xi$. For an integer $d\ge1$,
--   $$
--   \sum_{j=0}^{d-1}\mathrm{ph}_\xi\bigl(\mathrm{rot}(j/d)\,U\bigr)=\frac{d-1}2\,\|\xi\|^2+\mathrm{ph}_\xi\bigl(U^d\bigr).
--   $$
--
--   So the phase of $U^d$ is determined by the phases of the rotations of $U$ by $d$-th roots of unity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseGrids.lean#L98-L137

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

theorem OAI.KervaireSpectral.sum_vectorPhase_grid (U : Operator H) (hU : U ∈ unitary (Operator H))
    (d : ℕ) (hd : 0 < d) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (pow_mem hU d)
    let _ := fun j : Fin d => isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨scalarRotation ((j.val : ℝ)/d), scalarRotation_unitary _⟩ hU)
    (∑ j : Fin d, vectorPhase (scalarRotation ((j.val : ℝ)/d) • U) ξ) =
      ((d : ℝ)-1)/2 * ‖ξ‖^2 + vectorPhase (U^d) ξ := by sorry
