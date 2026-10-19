-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_trace_mul_eq_sum_tsum
-- name    : OAI.KervaireMatrix.trace_mul_eq_sum_tsum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:57:57.532191+00:00
-- url     : https://prove2.me/theorems/5ca59125-9f2f-4ebd-b9b4-2c54dd2e7a54
-- title:
--   Matrix coefficients of the trace of a product
-- statement:
--   Let $A$ be a group, $\ell^2(D\times A)$ the direct sum of $|D|$ copies of $\ell^2(A)$ for a finite set $D$, and call an operator equivariant if it commutes with the diagonal right translations $\delta_{(i,x)}\mapsto\delta_{(i,xa^{-1})}$. The trace is $\mathrm{Tr}(T)=\sum_{i\in D}\langle\delta_{(i,1)},T\delta_{(i,1)}\rangle$. If $S$ is equivariant, then for every bounded $T$,
--   $$
--   \mathrm{Tr}(ST)=\sum_{i,j\in D}\ \sum_{x\in A}S\delta_{(j,1)}(i,x^{-1})\;T\delta_{(i,1)}(j,x).
--   $$
--
--   The inner sum over the possibly uncountable group converges absolutely.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MatrixTrace.lean#L92-L109

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

theorem OAI.KervaireMatrix.trace_mul_eq_sum_tsum {S T : Operator D A} (hS : InCommutant S) :
    trace (S*T) = ∑ i : D, ∑ j : D, ∑' x : A,
      S (delta (j,1)) (i,x⁻¹) * T (delta (i,1)) (j,x) := by sorry
