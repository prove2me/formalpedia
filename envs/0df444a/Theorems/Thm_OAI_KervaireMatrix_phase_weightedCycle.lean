-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_weightedCycle
-- name    : OAI.KervaireMatrix.phase_weightedCycle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:04:01.677221+00:00
-- url     : https://prove2.me/theorems/df6e5833-1a16-41e3-ab9f-a98bfff0df0e
-- title:
--   Phase of a cyclic weighted shift
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. Here $\mathrm{ph}_\xi$ integrates the fractional part of $\arg z/2\pi$ against the spectral measure of $\xi$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a:D\to A$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,\,a_dx)}$. For the cyclic weighted shift on $n+1$ positions,
--   $$
--   \mathrm{Ph}\bigl(W(\mathrm{rot},u,a)\bigr)=\frac n2+\mathrm{gph}_{u_n\cdots u_0}\bigl(a_n\cdots a_1a_0\bigr),
--   $$
--   where $\mathrm{gph}$ is the group phase. So the phase depends only on the total scalar weight and the product of labels around the cycle.
--
--   This is the holonomy formula: a cyclic shift has phase $\frac n2$ plus the group phase of its holonomy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean#L344-L368

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
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

theorem OAI.KervaireMatrix.phase_weightedCycle (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    phase (weightedShift (finRotate (n+1)) u a) = (n : ℝ)/2 +
      groupPhase (orbitWeight (finRotate (n+1)) u (n+1) 0)
        (orbitWeight_mem (unitary ℂ) _ u hu _ _) (orbitWeight (finRotate (n+1)) a (n+1) 0) := by sorry
