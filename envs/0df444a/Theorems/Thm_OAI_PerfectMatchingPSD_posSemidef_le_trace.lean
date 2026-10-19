-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_posSemidef_le_trace
-- name    : OAI.PerfectMatchingPSD.posSemidef_le_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:13:45.638873+00:00
-- url     : https://prove2.me/theorems/1fe33c2e-26f2-40d9-9fe9-5871a27a4ba9
-- title:
--   A positive semidefinite matrix is dominated by its trace times the identity
-- statement:
--   Let $R$ be a finite index set and let $A$ be a real symmetric positive semidefinite matrix indexed by $R\times R$. Write $X\preceq Y$ for the Loewner order, meaning that $Y-X$ is positive semidefinite.
--
--   **Theorem.**
--   $$A\preceq\operatorname{tr}(A)\,I.$$
--
--   Equivalently, the largest eigenvalue of a positive semidefinite matrix is at most its trace, so $x^{\mathsf T}Ax\le\operatorname{tr}(A)\,\|x\|^2$ for all vectors $x$. In particular a density matrix ($\rho\succeq0$, $\operatorname{tr}\rho=1$) satisfies $\rho\preceq I$, so $\operatorname{tr}(\rho X)\le\operatorname{tr}X$ for every positive semidefinite $X$. The dimension bound for nearly perfect bit tests uses it in exactly this form.
--
--   **Formalization Note** The Loewner order is the `MatrixOrder` instance on `Matrix R R ℝ`, and the right-hand side is `A.trace • (1 : Matrix R R ℝ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SquareRootDisturbance.lean#L73-L92

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
universe u_1
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {R : Type u_1} [Fintype R] [DecidableEq R]

theorem OAI.PerfectMatchingPSD.posSemidef_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix R R ℝ) := by sorry
