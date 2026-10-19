-- Prove2me | Theorems.Thm_OAI_AffinePSD_evaluationCone_isClosed_of_diagonal
-- name    : OAI.AffinePSD.evaluationCone_isClosed_of_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:16:05.390757+00:00
-- url     : https://prove2.me/theorems/67495c34-5b63-4174-a473-cefd4afe6092
-- title:
--   The evaluation cone is closed when the family sums to a diagonal matrix
-- statement:
--   Let $I$ and $R$ be finite index sets and $(B_i)_{i\in I}$ a family of real $R\times R$ matrices. The evaluation map is $\mathrm{ev}_B(A)=(\operatorname{tr}(AB_i))_{i\in I}$, and the evaluation cone is $\mathrm{ev}_B(\{A:A\succeq0\})\subseteq\mathbb{R}^I$, the image of the positive semidefinite matrices. Assume every $B_i$ is positive semidefinite and $\sum_iB_i=\operatorname{diag}(d)$ is diagonal.
--
--   Then the evaluation cone is closed:
--   $$
--   \{\mathrm{ev}_B(A):A\succeq0\}\ \text{is a closed subset of }\mathbb{R}^I .
--   $$
--
--   Images of closed cones under linear maps need not be closed. Here the positive semidefinite family supplies the compactness that makes the image closed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/DiagonalCone.lean#L13-L50

import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift

open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

theorem OAI.AffinePSD.evaluationCone_isClosed_of_diagonal (B : I → Matrix R R ℝ)
    (hB : ∀ i, (B i).PosSemidef) (d : R → ℝ)
    (hs : ∑ i, B i = diagonal d) : IsClosed (evaluationCone B) := by sorry
