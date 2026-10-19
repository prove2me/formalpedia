-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_exists_incidence_of_homotopic
-- name    : OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:40:57.537824+00:00
-- url     : https://prove2.me/theorems/d3dfcd14-2987-44a9-99aa-da3dbeadd3d4
-- title:
--   Maps homotopic to the model hit the identity incidence
-- statement:
--   Let $K,R$ be finite sets with $K$ nonempty, and let $M_I$ denote complex $I\times I$ matrices. Let $F:M_K\to M_{K\sqcup R}$ be smooth, sending unitaries to unitaries. Suppose $F$ is smoothly homotopic, through such maps and by a finite chain of elementary homotopies, to the model map $X\mapsto\mathrm{diag}(X,-1)$. Then there are unitaries $X\in U(K)$, $P\in U(K\sqcup R)$ and $Q\in U(R)$ with
--   $$
--   F(X)\,P\,\mathrm{diag}(1,Q^*)\,P^*=1 .
--   $$
--
--   Equivalently $F(X)=P\,\mathrm{diag}(1,Q)\,P^*$, so $F(X)$ fixes a subspace of dimension $|K|$. This is a degree argument on the unitary group of $M_K\times M_{K\sqcup R}\times M_R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/CurrentExistence.lean#L143-L157

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
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

theorem OAI.KervaireIncidenceCurrent.exists_incidence_of_homotopic [Nonempty K]
    (F : UMap (Mat K) (Mat (K ⊕ R))) (hF : Homotopic modelMap F) :
    ∃ p : unitary (Alg K R), incidence (timeless F) (0,(p : Alg K R)) = 1 := by sorry
