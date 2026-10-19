-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_direction_bracket
-- name    : OAI.KervaireIncidenceCurrent.fderiv_direction_bracket
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:33:21.851254+00:00
-- url     : https://prove2.me/theorems/2c43ddc9-109e-43ad-993a-e8c58e27dce3
-- title:
--   Brackets of horizontal directions under the incidence differential
-- statement:
--   For finite index sets $K,R$ and a map $f:\mathbb R\times M_K\to M_{K\sqcup R}$, where $M_I$ denotes complex $I\times I$ matrices, the incidence map is
--   $$
--   \mathrm{inc}_f(t;X,P,Q)=f(t,X)\,P\,\mathrm{diag}(1,Q^*)\,P^*,
--   $$
--   defined for $X\in M_K$, $P\in M_{K\sqcup R}$ and $Q\in M_R$.
--
--   At a unitary point $p=(X,P,Q)$ of the algebra $M_K\times M_{K\sqcup R}\times M_R$, consider horizontal vectors $h,g$, triples of a skew $K$-matrix, a skew $R$-matrix and an $R\times K$ matrix. The differential of the incidence map sends the commutator direction $p[\mathrm{dir}\,h,\mathrm{dir}\,g]$ to the image of the direction of their effective bracket:
--   $$
--   d\,\mathrm{inc}_f\bigl(p[\mathrm{dir}\,h,\mathrm{dir}\,g]\bigr)=d\,\mathrm{inc}_f\bigl(p\,\mathrm{dir}(\{h,g\}_Q)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean#L146-L177

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

open OAI OAI.KervaireIncidenceCurrent
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
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

theorem OAI.KervaireIncidenceCurrent.fderiv_direction_bracket {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (p : unitary (Alg K R)) (h g : Horizontal K R) :
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*((direction h : Alg K R)*(direction g : Alg K R)-
        (direction g : Alg K R)*(direction h : Alg K R))) =
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*(direction (effectiveBracket ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩ h g) : Alg K R)) := by sorry
