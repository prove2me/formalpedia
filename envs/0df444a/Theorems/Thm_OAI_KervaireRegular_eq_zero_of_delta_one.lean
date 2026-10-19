-- Prove2me | Theorems.Thm_OAI_KervaireRegular_eq_zero_of_delta_one
-- name    : OAI.KervaireRegular.eq_zero_of_delta_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:57:19.975053+00:00
-- url     : https://prove2.me/theorems/3f3fdf8e-4f49-40d4-a27b-1e38fcfd3775
-- title:
--   Equivariant operators are determined by one vector
-- statement:
--   Let $A$ be a group and $T$ a bounded operator on $\ell^2(A)$ commuting with all right translations $R(a)\delta_x=\delta_{xa^{-1}}$. If $T\delta_1=0$, then
--   $$
--   T=0 .
--   $$
--
--   So $\delta_1$ is a separating vector for the group von Neumann algebra.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RegularOperators.lean#L185-L199

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
variable {α β γ : Type*}
variable {A : Type*} [Group A]

theorem OAI.KervaireRegular.eq_zero_of_delta_one {T : Operator A} (hT : InCommutant T)
    (h : T (delta 1) = 0) : T = 0 := by sorry
