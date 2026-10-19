-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_weightedShift_grid
-- name    : OAI.KervaireMatrix.phase_weightedShift_grid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:01:21.03357+00:00
-- url     : https://prove2.me/theorems/f35bd43c-14dd-4e56-96ef-7bb052b1bf23
-- title:
--   Phase of a cyclic weighted shift through its power
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}(U)=\sum_{i\in D}\mathrm{ph}_{\delta_{(i,1)}}(U)$ the traced fractional phase of a unitary on $\ell^2(D\times A)$. Here $\mathrm{ph}_\xi$ integrates the fractional part of $\arg z/2\pi$ against the spectral measure of $\xi$. For a permutation $\sigma$ of $D$, unit scalars $u$ and labels $a:D\to A$, the weighted shift $W(\sigma,u,a)$ sends $\delta_{(d,x)}$ to $u_d\,\delta_{(\sigma d,\,a_dx)}$. For the cyclic weighted shift $W=W(\mathrm{rot},u,a)$ on $n+1$ positions,
--   $$
--   (n+1)\,\mathrm{Ph}(W)=\frac{(n+1)\,n}2+\mathrm{Ph}\bigl(W^{n+1}\bigr).
--   $$
--
--   The phase of the shift is thus reduced to the phase of its power $W^{n+1}$, which is diagonal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean#L72-L93

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
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

theorem OAI.KervaireMatrix.phase_weightedShift_grid (n : ℕ) (u : Fin (n+1) → ℂ)
    (a : Fin (n+1) → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary (pow_mem (weightedShift_unitary (finRotate (n+1)) u a hu) (n+1))
    (n+1 : ℝ) * KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) =
      (n+1 : ℝ) * (n : ℝ)/2 +
        KervaireMatrix.phase ((weightedShift (finRotate (n+1)) u a)^(n+1)) := by sorry
