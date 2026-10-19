-- Prove2me | Theorems.Thm_OAI_KervaireMixing_phase_upper_of_fixed
-- name    : OAI.KervaireMixing.phase_upper_of_fixed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:47:30.624847+00:00
-- url     : https://prove2.me/theorems/c7e81922-0ed6-4bbe-aae3-feb8054d3fc9
-- title:
--   Phase upper bound from a fixed space of the mixed band
-- statement:
--   Let $A$ be a group, $I,K$ nonempty finite sets, $\rho$ a permutation of $I$ and $a:I\to A$. Let $S$ be the coefficient shift on $\ell^2(\mathrm{Slots}\times A)$, which moves positive slots forward and negative slots backward along $\rho$ with coefficients from $a$. Slots are $(K\sqcup K)\times I$: a disk number in $K$, a kind (positive or negative) and a position in $I$. For $X\in U(K)$ the scalar mixer is the block-diagonal matrix $Q_X=\bigoplus_{i\in I}\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$, which exchanges the two kinds at each position. Let $T$ be a self-adjoint unitary on slots and $X\in U(K)$ with $2|K|\le\mathrm{fix}(Q_XT)$, the dimension of the fixed space. Then the traced fractional phase satisfies
--   $$
--   \mathrm{Ph}\bigl(S\,(T\otimes1)\bigr)\le\frac32\,|I|\,|K|-|K| .
--   $$
--
--   Here $T\otimes1$ acts on the slot coordinate only. The fixed space of the mixed band matrix lowers the bound by $|K|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Traversal.lean#L279-L329

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
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal

open OAI OAI.KervaireMixing
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
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
attribute [local instance] OAI.KervaireMixing.instDecidableEqSlot
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]

theorem OAI.KervaireMixing.phase_upper_of_fixed (ρ : Equiv.Perm I) (a : I → A)
    (T : Matrix (Slot I K) (Slot I K) ℂ)
    (hT : T ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ)) (hTs : star T = T)
    (X : Matrix.unitaryGroup K ℂ)
    (hfix : 2 * Fintype.card K ≤ fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) * T)) :
    let _ := isStarNormal_of_mem_unitary
      (mul_mem (S_unitary (K := K) ρ a) (scalarTensor_mem_unitary (A := A) hT))
    KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤
      3 / 2 * (Fintype.card I : ℝ) * Fintype.card K - Fintype.card K := by sorry
