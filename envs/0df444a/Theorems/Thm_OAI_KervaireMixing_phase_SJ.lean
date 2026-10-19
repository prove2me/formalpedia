-- Prove2me | Theorems.Thm_OAI_KervaireMixing_phase_SJ
-- name    : OAI.KervaireMixing.phase_SJ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:16:37.276406+00:00
-- url     : https://prove2.me/theorems/fd2c58da-da92-4ce2-8e40-66c81927a8da
-- title:
--   Phase of the mixed coefficient shift
-- statement:
--   Let $S$ be the coefficient shift on slots $(K\sqcup K)\times I$ for a relator with positions $I$ and coefficients $a$. Let $J$ be the scalar mixer built from $X\in U(K)$, with $I,K$ nonempty. Then the traced phase of $SJ$ on $\ell^2(\mathrm{Slots}\times A)$ is
--   $$
--   \mathrm{Ph}(SJ)=\frac{|I|\,|K|}2 .
--   $$
--
--   This value is independent of the relator coefficients and of $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MixingOperators.lean#L144-L161

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
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

theorem OAI.KervaireMixing.phase_SJ [Nonempty I] [Nonempty K]
    (ρ : Equiv.Perm I) (a : I → A) (X : Matrix.unitaryGroup K ℂ) :
    let _ := isStarNormal_of_mem_unitary
      ((unitary _).mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X))
    KervaireMatrix.phase (S ρ a * J (I := I) (X : Matrix K K ℂ)) =
      (Fintype.card I : ℝ) * Fintype.card K / 2 := by sorry
