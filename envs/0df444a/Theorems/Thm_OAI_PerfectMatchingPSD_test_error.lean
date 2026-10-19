-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_test_error
-- name    : OAI.PerfectMatchingPSD.test_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:13:03.95528+00:00
-- url     : https://prove2.me/theorems/8b7a2eef-98d5-4a81-ac22-d3d3a1296924
-- title:
--   An effect accepting a density matrix with probability at least $1-\varepsilon$ moves its square root by at most $\sqrt{\varepsilon}$ in Frobenius norm
-- statement:
--   Let $R$ be a finite index set and consider real square matrices indexed by $R$. Let $\rho$ be a real density matrix, i.e. $\rho$ is symmetric positive semidefinite with $\operatorname{tr}\rho=1$. Let $F$ be an *effect*: $0\preceq F\preceq I$ in the Loewner order, where $X\preceq Y$ means that $Y-X$ is positive semidefinite. Let $\varepsilon\ge0$ and assume $\operatorname{tr}(\rho F)\ge1-\varepsilon$.
--
--   **Theorem.**
--   $$\bigl\|(F-I)\sqrt{\rho}\bigr\|_F\le\sqrt{\varepsilon},$$
--   where $\sqrt{\rho}$ is the positive semidefinite square root of $\rho$ and $\|X\|_F=\bigl(\sum_{k,l}X_{kl}^2\bigr)^{1/2}$ is the Frobenius norm.
--
--   This is a gentle-measurement type estimate. An effect that accepts the state $\rho$ with probability at least $1-\varepsilon$ acts on $\sqrt\rho$ almost like the identity, with an error of order $\sqrt\varepsilon$ in Frobenius norm. It makes it possible to apply many nearly certain tests one after another while keeping track of the accumulated disturbance. In this formalization it is used for the dimension bound for states whose bits can all be decoded almost perfectly.
--
--   **Formalization Note** The Loewner order is the `MatrixOrder` instance on `Matrix R R ℝ`, so `0 ≤ F` already forces $F$ to be symmetric. The square root is `CFC.sqrt ρ` and the norm is the Frobenius norm from the scope `Matrix.Norms.Frobenius`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SquareRootDisturbance.lean#L51-L71

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

theorem OAI.PerfectMatchingPSD.test_error {ρ F : Matrix R R ℝ} (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hF : 0 ≤ F) (hF₁ : F ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : 1-ε ≤ (ρ*F).trace) :
    ‖(F-1)*CFC.sqrt ρ‖ ≤ Real.sqrt ε := by sorry
