-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_trace_mul_comm
-- name    : OAI.KervaireMatrix.trace_mul_comm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:58:45.538496+00:00
-- url     : https://prove2.me/theorems/185f53ba-6ede-4a3a-b4a1-e52f8e7e4ea1
-- title:
--   The matrix trace is tracial on equivariant operators
-- statement:
--   Let $A$ be a group, $\ell^2(D\times A)$ the direct sum of $|D|$ copies of $\ell^2(A)$ for a finite set $D$, and call an operator equivariant if it commutes with the diagonal right translations $\delta_{(i,x)}\mapsto\delta_{(i,xa^{-1})}$. The trace is $\mathrm{Tr}(T)=\sum_{i\in D}\langle\delta_{(i,1)},T\delta_{(i,1)}\rangle$. For equivariant operators $S,T$,
--   $$
--   \mathrm{Tr}(ST)=\mathrm{Tr}(TS).
--   $$
--
--   So $\mathrm{Tr}$ is a trace on matrices over the group von Neumann algebra of an arbitrary group.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean#L111-L124

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

open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireRegular
variable {D A : Type*} [Group A]
variable [Fintype D]

theorem OAI.KervaireMatrix.trace_mul_comm {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    trace (S*T) = trace (T*S) := by sorry
