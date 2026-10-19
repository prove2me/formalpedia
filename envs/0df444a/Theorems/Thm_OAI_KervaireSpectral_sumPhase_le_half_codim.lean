-- Prove2me | Theorems.Thm_OAI_KervaireSpectral_sumPhase_le_half_codim
-- name    : OAI.KervaireSpectral.sumPhase_le_half_codim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:10:39.616216+00:00
-- url     : https://prove2.me/theorems/884adb74-d7e9-45b9-9529-a69f52ae9680
-- title:
--   Phase bound for a unitary conjugate to its adjoint
-- statement:
--   Let $U,Q$ be unitaries on a finite-dimensional Hilbert space $H$ with $QUQ^*=U^*$, and suppose $U$ fixes every vector of a subspace $E$. Then for any orthonormal basis,
--   $$
--   \mathrm{Ph}(U)\le\frac{\dim H-\dim E}2 .
--   $$
--
--   Large fixed spaces force the phase of such a self-conjugate unitary to be small.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean#L174-L192

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

theorem OAI.KervaireSpectral.sumPhase_le_half_codim (U Q : Operator H)
    (hU : U ∈ unitary (Operator H)) (hQ : Q ∈ unitary (Operator H))
    (hconj : Q*U*star Q = star U)
    (b : OrthonormalBasis ι ℂ H) (E : Submodule ℂ H)
    (hE : ∀ v : E, U (v : H) = (v : H)) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U b ≤ ((Module.finrank ℂ H : ℝ) - Module.finrank ℂ E) / 2 := by sorry
