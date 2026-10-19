-- Prove2me | Theorems.Thm_OAI_AffinePSD_exists_psd_evaluation
-- name    : OAI.AffinePSD.exists_psd_evaluation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:20:21.836497+00:00
-- url     : https://prove2.me/theorems/8f443fc8-5e95-40a5-8d48-3594ab8f86f6
-- title:
--   Duality for trace evaluations: nonnegativity on PSD combinations gives a PSD realiser
-- statement:
--   Let $I$ and $R$ be finite index sets and $(B_i)_{i\in I}$ a family of real $R\times R$ matrices. The evaluation map is $\mathrm{ev}_B(A)=(\operatorname{tr}(AB_i))_{i\in I}$, and the evaluation cone is $\mathrm{ev}_B(\{A:A\succeq0\})\subseteq\mathbb{R}^I$, the image of the positive semidefinite matrices. Assume every $B_i$ is positive semidefinite. Let $y\in\mathbb{R}^I$ satisfy $\sum_ic_iy_i\ge0$ for every $c\in\mathbb{R}^I$ with $\sum_ic_iB_i\succeq0$. Then there is $A\succeq0$ with
--   $$
--   \operatorname{tr}(AB_i)=y_i\quad\text{for all }i\in I .
--   $$
--
--   This is the conic duality statement behind positive semidefinite certificates. It reduces producing a factor to checking nonnegativity against PSD combinations of the family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/PSDDuality.lean#L44-L76

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

theorem OAI.AffinePSD.exists_psd_evaluation (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (y : I → ℝ)
    (hy : ∀ c : I → ℝ, (∑ i, c i • B i).PosSemidef → 0 ≤ ∑ i, c i * y i) :
    ∃ A : Matrix R R ℝ, A.PosSemidef ∧ evaluation B A = y := by sorry
