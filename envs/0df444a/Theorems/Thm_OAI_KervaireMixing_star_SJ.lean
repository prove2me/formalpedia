-- Prove2me | Theorems.Thm_OAI_KervaireMixing_star_SJ
-- name    : OAI.KervaireMixing.star_SJ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:16:04.584846+00:00
-- url     : https://prove2.me/theorems/dfdc5688-0252-4fb5-9f68-d3da9fbfd375
-- title:
--   The product of the coefficient shift and the mixer is self-adjoint
-- statement:
--   Let $S$ be the coefficient shift on slots $(K\sqcup K)\times I$. It moves positive slots forward and negative slots backward along the relator, with labels $a_i^{-1}$ and $a_{\rho^{-1}i}$. Let $J$ be the scalar mixer $\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$ at each position. Then
--   $$
--   (SJ)^*=SJ .
--   $$
--
--   So $SJ$ is a self-adjoint unitary, and $\mathrm{Ph}(SJ)$ can be computed from its fixed space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean#L119-L137

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
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

theorem OAI.KervaireMixing.star_SJ (ρ : Equiv.Perm I) (a : I → A) (X : Matrix K K ℂ) :
    star (S ρ a * J (I := I) X) = S ρ a * J (I := I) X := by sorry
