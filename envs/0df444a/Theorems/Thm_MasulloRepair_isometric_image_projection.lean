-- Prove2me | Theorems.Thm_MasulloRepair_isometric_image_projection
-- name    : MasulloRepair.isometric_image_projection
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T19:28:18.967899+00:00
-- url     : https://prove2.me/theorems/aac5646c-2219-40d1-adc5-c8109f3827cc
-- title:
--   Orthogonal projection onto the image of a closed subspace under an isometry
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces, let $U:H\to K$ be a linear isometric embedding, and let $P\subset H$ be a closed linear subspace. Write $P_P$ and $P_{U(P)}$ for the corresponding orthogonal projections, and $U^*$ for the Hilbert-space adjoint. Then
--   $$P_{U(P)}=U P_P U^*.$$
--   The equality holds as an operator on all of $K$, including the orthogonal complement of the range of $U$. Surjectivity of $U$ is not required.
--
--   This is the projection identity needed to factor a common isometric multiplier out of a difference of range projections. In Lean, completeness of the subspace expresses closedness; completeness of its isometric image follows automatically.
-- source:
--   Auxiliary operator theorem for Yi's 'Actual global unit-shell increment at fixed incoming bandwidth', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02, step 5 ('Trace on the actual limiting projections'). This is an explicit general Hilbert-space lemma supporting the proposed repair, rather than a formalization of the full global trace formula. Mathlib Analysis/InnerProductSpace/Projection/Basic.lean, Submodule.eq_starProjection_of_mem_of_inner_eq_zero; Analysis/InnerProductSpace/Adjoint.lean, at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace

theorem MasulloRepair.isometric_image_projection {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (P : Submodule ℂ H)
    [CompleteSpace P] :
    (P.map (U : H →ₗ[ℂ] K)).starProjection =
      U.toContinuousLinearMap ∘L P.starProjection ∘L U.toContinuousLinearMap.adjoint := by sorry
