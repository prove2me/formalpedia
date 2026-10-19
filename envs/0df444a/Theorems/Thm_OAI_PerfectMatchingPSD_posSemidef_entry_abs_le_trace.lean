-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_posSemidef_entry_abs_le_trace
-- name    : OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:18:16.486876+00:00
-- url     : https://prove2.me/theorems/3fac6887-67be-4489-b08b-e42dcdbe3d37
-- title:
--   Every entry of a positive semidefinite matrix is bounded in absolute value by its trace
-- statement:
--   Let $R$ be a finite index set and let $A$ be a real symmetric positive semidefinite matrix indexed by $R\times R$.
--
--   **Theorem.** For all $i,j\in R$,
--   $$|A_{ij}|\le\operatorname{tr}A.$$
--
--   Once the traces of the factors in a PSD factorization have been normalized, this lemma bounds every entry of every factor uniformly. For instance, $\operatorname{tr}B\le r$ forces $|B_{ij}|\le r$. Such entrywise bounds are needed to control averages and interpolations of factor matrices.
--
--   **Formalization Note** Positive semidefiniteness is Mathlib's `Matrix.PosSemidef` for `Matrix R R ℝ`, which includes symmetry; no assumption $i\neq j$ is made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatrixBounds.lean#L50-L79

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests

open OAI OAI.PerfectMatchingPSD
universe u_1 u_2
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

theorem OAI.PerfectMatchingPSD.posSemidef_entry_abs_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) (i j : R) :
    |A i j| ≤ A.trace := by sorry
