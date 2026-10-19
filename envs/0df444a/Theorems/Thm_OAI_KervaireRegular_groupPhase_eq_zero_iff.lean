-- Prove2me | Theorems.Thm_OAI_KervaireRegular_groupPhase_eq_zero_iff
-- name    : OAI.KervaireRegular.groupPhase_eq_zero_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:04:43.960379+00:00
-- url     : https://prove2.me/theorems/ccb74a15-0384-472a-9979-0a8b6069cb17
-- title:
--   The group phase detects the identity
-- statement:
--   For a group $A$, a unit scalar $z$ and $a\in A$, the group phase is $\mathrm{gph}_z(a)=\mathrm{ph}_{\delta_1}(zL(a))$, the fractional phase at $\delta_1$ of the rotated left translation on $\ell^2(A)$. With $z=1$,
--   $$
--   \mathrm{gph}_1(a)=0\iff a=1 .
--   $$
--
--   This faithfulness of the phase turns phase identities into the triviality of group elements.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean#L34-L75

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

open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

theorem OAI.KervaireRegular.groupPhase_eq_zero_iff (a : A) : groupPhase 1 (one_mem _) a = 0 ↔ a = 1 := by sorry
