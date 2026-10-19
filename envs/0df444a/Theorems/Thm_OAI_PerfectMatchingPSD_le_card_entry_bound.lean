-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_le_card_entry_bound
-- name    : OAI.PerfectMatchingPSD.le_card_entry_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:17:34.266809+00:00
-- url     : https://prove2.me/theorems/2ad52521-ee6c-48c0-854c-4aeeefb36a70
-- title:
--   An entrywise bound $|E_{ij}|\le b$ implies the Loewner bound $E\preceq r\,b\,I$
-- statement:
--   Let $R$ be a finite index set with $r=|R|$ elements, and let $E$ be a real symmetric matrix indexed by $R\times R$. Let $b\ge0$ satisfy $|E_{ij}|\le b$ for all $i,j\in R$. Write $X\preceq Y$ for the Loewner order ($Y-X$ positive semidefinite).
--
--   **Theorem.**
--   $$E\preceq r\,b\,I.$$
--
--   Equivalently, $x^{\mathsf T}Ex\le r\,b\,\|x\|^2$ for every $x\in\mathbb{R}^R$, so every eigenvalue of $E$ is at most $rb$. This crude, dimension-explicit operator bound turns entrywise control of a symmetric matrix into domination by a multiple of the identity. Domination of this kind is needed when an interpolated combination of PSD factor matrices has to be compared with the identity.
--
--   **Formalization Note** Symmetry is `E.IsHermitian` for a real matrix, and the right-hand side is `((Fintype.card R : ℝ) * b) • (1 : Matrix R R ℝ)` in the `MatrixOrder` Loewner order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatrixBounds.lean#L23-L48

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

theorem OAI.PerfectMatchingPSD.le_card_entry_bound {E : Matrix R R ℝ} (hE : E.IsHermitian)
    {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i j, |E i j| ≤ b) :
    E ≤ ((Fintype.card R : ℝ)*b) • (1 : Matrix R R ℝ) := by sorry
