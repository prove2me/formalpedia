-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_sumPhase_add_star_le_codim
-- name    : OAI.KervaireSpectral.sumPhase_add_star_le_codim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:09:02.755704+00:00
-- url     : https://prove2.me/theorems/a6dbe2b2-6c26-446a-8957-97ef62300108
-- title:
--   Phase of a unitary fixing a subspace
-- statement:
--   Let $U$ be a unitary on a finite-dimensional Hilbert space $H$ fixing every vector of a subspace $E$. For any orthonormal basis $(b_j)$, with $\mathrm{Ph}(U)=\sum_j\mathrm{ph}_{b_j}(U)$,
--   $$
--   \mathrm{Ph}(U)+\mathrm{Ph}(U^*)\le\dim E^\perp .
--   $$
--
--   The traced phase does not depend on the chosen orthonormal basis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean#L100-L133

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
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem OAI.KervaireSpectral.sumPhase_add_star_le_codim (U : Operator H) (hU : U ∈ unitary (Operator H))
    (b : OrthonormalBasis ι ℂ H) (E : Submodule ℂ H)
    (hE : ∀ v : E, U (v : H) = (v : H)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (Unitary.star_mem hU)
    sumPhase U b + sumPhase (star U) b ≤ (Module.finrank ℂ Eᗮ : ℝ) := by sorry
