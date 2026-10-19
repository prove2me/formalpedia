-- Prove2me | Theorems.Thm_OAI_KervaireRegular_groupPhase_conjugate
-- name    : OAI.KervaireRegular.groupPhase_conjugate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:01:57.454631+00:00
-- url     : https://prove2.me/theorems/3b620c98-3578-4f68-bb10-944cacab7109
-- title:
--   Group phases are conjugation invariant
-- statement:
--   For a group $A$, a unit scalar $z$ and $a\in A$, the group phase is $\mathrm{gph}_z(a)=\mathrm{ph}_{\delta_1}(zL(a))$, the fractional phase at $\delta_1$ of the rotated left translation on $\ell^2(A)$. For all $a,b\in A$,
--   $$
--   \mathrm{gph}_z(bab^{-1})=\mathrm{gph}_z(a).
--   $$
--
--   So the group phase is a class function on $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean#L161-L178

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
open scoped Classical
variable {A : Type*} [Group A]

theorem OAI.KervaireRegular.groupPhase_conjugate (z : ℂ) (hz : z ∈ unitary ℂ) (a b : A) :
    groupPhase z hz (b*a*b⁻¹) = groupPhase z hz a := by sorry
