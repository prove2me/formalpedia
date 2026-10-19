-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_vectorPhase_rotation
-- name    : OAI.KervaireSpectral.vectorPhase_rotation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:54:33.476833+00:00
-- url     : https://prove2.me/theorems/c5002d6f-4ee9-43ec-80c1-27dfc5546ec4
-- title:
--   Phase of a rotated unitary
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, let $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ be its fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$ and $\mu_\xi$ the spectral measure of $\xi$. For $x\in\mathbb R$ and $\mathrm{rot}(x)=e^{2\pi ix}$,
--   $$
--   \mathrm{ph}_\xi\bigl(\mathrm{rot}(x)\,U\bigr)=\int\mathrm{ph}\bigl(\mathrm{rot}(x)\,z\bigr)\,d\mu_\xi(z).
--   $$
--
--   Rotating a unitary rotates its spectral measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseNaturality.lean#L143-L161

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

theorem OAI.KervaireSpectral.vectorPhase_rotation (U : Operator H) (hU : U ∈ unitary (Operator H))
    (x : ℝ) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨scalarRotation x,
      scalarRotation_unitary x⟩ hU)
    vectorPhase (scalarRotation x • U) ξ =
      ∫ z, phase (scalarRotation x * (z : ℂ)) ∂vectorMeasure U ξ := by sorry
