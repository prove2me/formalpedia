-- Prove2me | Theorems.Thm_OAI_AffinePSD_affine_slack_certificate
-- name    : OAI.AffinePSD.affine_slack_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:22:30.572182+00:00
-- url     : https://prove2.me/theorems/d4663b21-2284-48dd-aa24-ee36a6748d1a
-- title:
--   An affine function nonnegative on a spectrahedron and tight at one point has a PSD trace certificate
-- statement:
--   Let $R$ and $I$ be finite and let $L$ be an affine subspace of the real $R\times R$ matrices. Let $(B_i)_{i\in I}$ be positive semidefinite matrices lying in $L$. Let $f$ be a real affine function on matrices with $f(X)\ge0$ for every positive semidefinite $X\in L$, and suppose $f(B_{i_0})=0$ for some $i_0$. Then there is $A\succeq0$ with
--   $$
--   \operatorname{tr}(AB_i)=f(B_i)\quad\text{for all }i\in I .
--   $$
--
--   The tightness at one point turns the affine function into a linear one on the cone spanned by the family. This is how each slack inequality of a polytope with a spectrahedral lift yields one factor of a PSD factorization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AffineCertificate.lean#L12-L49

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

theorem OAI.AffinePSD.affine_slack_certificate (L : AffineSubspace ℝ (Matrix R R ℝ))
    (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef) (hBL : ∀ i, B i ∈ L)
    (f : Matrix R R ℝ →ᵃ[ℝ] ℝ)
    (hn : ∀ X ∈ L, X.PosSemidef → 0 ≤ f X)
    (i₀ : I) (hz : f (B i₀) = 0) :
    ∃ A : Matrix R R ℝ, A.PosSemidef ∧ ∀ i, (A * B i).trace = f (B i) := by sorry
