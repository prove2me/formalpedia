-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_vectorPhase_involution
-- name    : OAI.KervaireSpectral.vectorPhase_involution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:13:02.653324+00:00
-- url     : https://prove2.me/theorems/5b048e71-c919-45f6-99e3-9a11301a9654
-- title:
--   Phase of a unitary involution
-- statement:
--   For a unitary $U$ on a Hilbert space and a vector $\xi$, $\mathrm{ph}_\xi(U)=\int\mathrm{ph}\,d\mu_\xi$ is the fractional phase at $\xi$, where $\mathrm{ph}(z)\in[0,1)$ is the fractional part of $\arg z/2\pi$. If $U$ is unitary with $U^2=1$, then for every vector $\xi$,
--   $$
--   \mathrm{ph}_\xi(U)=\frac{\mathrm{Re}\langle\xi,\xi\rangle-\mathrm{Re}\langle\xi,U\xi\rangle}4 .
--   $$
--
--   The spectrum lies in $\{1,-1\}$, where the phase is $0$ and $\frac12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean#L250-L274

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
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension

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
open scoped ComplexOrder
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

theorem OAI.KervaireSpectral.vectorPhase_involution (U : Operator H) (hU : U ∈ unitary (Operator H))
    (hUU : U ^ 2 = 1) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = ((vectorCLM ξ 1).re - (vectorCLM ξ U).re) / 4 := by sorry
