-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_exists_normalized_factors
-- name    : OAI.PerfectMatchingPSD.exists_normalized_factors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:12:14.662085+00:00
-- url     : https://prove2.me/theorems/2599d18b-dac9-4091-b9f9-f5e279c0cbd1
-- title:
--   Trace normalization of PSD factors by determinant maximization
-- statement:
--   Let $R$ be a finite index set with $r=|R|$ elements, and consider real $r\times r$ matrices indexed by $R$. *PSD* means symmetric positive semidefinite. Let $I$ be a nonempty finite set and $J$ a finite set. Let $A_j$ ($j\in J$) and $B_i$ ($i\in I$) be PSD matrices, and let $m\in\mathbb{R}$ satisfy $\operatorname{tr}(A_jB_i)\le m$ for all $j\in J$ and $i\in I$.
--
--   **Theorem.** There exist PSD matrices $A'_j$ ($j\in J$) and $B'_i$ ($i\in I$) such that for all $j\in J$ and $i\in I$
--   $$\operatorname{tr}(A'_jB'_i)=\operatorname{tr}(A_jB_i),\qquad \operatorname{tr}A'_j\le m+1,\qquad \operatorname{tr}B'_i\le r.$$
--
--   If a nonnegative matrix $S_{ji}=\operatorname{tr}(A_jB_i)$ has a PSD factorization of size $r$ and all its entries are at most $m$, the factorization can therefore be replaced by one of the same size with uniformly bounded traces: at most $m+1$ on the row side and at most the dimension $r$ on the column side. Combined with the bound of matrix entries by the trace, this gives uniform bounds on all entries of the factors. The PSD-rank lower bound for the perfect matching slack matrix needs exactly this kind of control.
--
--   **Formalization Note** The matrices have type `Matrix R R ℝ` with `[Fintype R] [DecidableEq R]`, and $r$ is `Fintype.card R`. PSD is Mathlib's `Matrix.PosSemidef`, which includes symmetry. Nonemptiness of $I$ is the instance `[Nonempty I]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/DeterminantNormalization.lean#L133-L185

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

open OAI OAI.PerfectMatchingPSD
universe u_1 u_2 u_3
open Matrix Set
variable {R : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype R] [DecidableEq R]
open scoped MatrixOrder

theorem OAI.PerfectMatchingPSD.exists_normalized_factors [Fintype I] [Nonempty I] [Fintype J]
    (A : J → Matrix R R ℝ) (B : I → Matrix R R ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (m : ℝ) (hpair : ∀ j i, (A j * B i).trace ≤ m) :
    ∃ (A' : J → Matrix R R ℝ) (B' : I → Matrix R R ℝ),
      (∀ j, (A' j).PosSemidef) ∧ (∀ i, (B' i).PosSemidef) ∧
      (∀ j i, (A' j * B' i).trace = (A j * B i).trace) ∧
      (∀ j, (A' j).trace ≤ m + 1) ∧
      (∀ i, (B' i).trace ≤ (Fintype.card R : ℝ)) := by sorry
