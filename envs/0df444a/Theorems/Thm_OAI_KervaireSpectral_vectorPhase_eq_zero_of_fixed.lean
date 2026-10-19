-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_vectorPhase_eq_zero_of_fixed
-- name    : OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:05:51.034385+00:00
-- url     : https://prove2.me/theorems/eca174c4-24cf-4848-afef-34961583fa15
-- title:
--   Fixed vectors have zero phase
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ is the fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$. If $U\xi=\xi$, then
--   $$
--   \mathrm{ph}_\xi(U)=0 .
--   $$
--
--   The spectral measure of a fixed vector is concentrated at $1$, where the fractional phase vanishes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean#L91-L107

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

theorem OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) (hξ : U ξ = ξ) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = 0 := by sorry
