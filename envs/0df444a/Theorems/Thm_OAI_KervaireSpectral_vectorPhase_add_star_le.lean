-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_vectorPhase_add_star_le
-- name    : OAI.KervaireSpectral.vectorPhase_add_star_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:06:29.513272+00:00
-- url     : https://prove2.me/theorems/06c7a490-2d07-4f8a-8b2c-0f9da9e9ed14
-- title:
--   Phases of a unitary and its adjoint
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ is the fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$. For every unitary $U$ and vector $\xi$,
--   $$
--   \mathrm{ph}_\xi(U)+\mathrm{ph}_\xi(U^*)\le\|\xi\|^2 .
--   $$
--
--   Pointwise, $\mathrm{ph}(z)+\mathrm{ph}(\bar z)$ is $1$ for $z\ne1$ and $0$ for $z=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean#L109-L133

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

open OAI OAI.KervaireSpectral
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.KervaireSpectral.vectorPhase_add_star_le (U : Operator H) (hU : U ∈ unitary (Operator H)) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    vectorPhase U ξ + vectorPhase (star U) ξ ≤ ‖ξ‖^2 := by sorry
