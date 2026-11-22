-- Prove2me | Theorems.Thm_MasulloRepair_relative_projection_trace_isometry
-- name    : MasulloRepair.relative_projection_trace_isometry
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T19:28:33.590285+00:00
-- url     : https://prove2.me/theorems/4946095c-2f2d-4ab7-bb91-6a8d2ec386da
-- title:
--   A common isometric multiplier cancels from a nuclear relative projection trace
-- statement:
--   Let $H,K$ be complete complex Hilbert spaces, $U:H\to K$ a linear isometric embedding, $A:H\to H$ and $B:K\to K$ bounded linear operators, and $P,Q\subset H$ closed linear subspaces. Suppose
--   $$BU=UA,\qquad T=A(P_P-P_Q)\text{ is nuclear}.$$
--   Set
--   $$S=B(P_{U(P)}-P_{U(Q)}).$$
--   Then the full operators satisfy
--   $$S=UTU^*,\qquad S\text{ is nuclear},\qquad \operatorname{Tr}_K(S)=\operatorname{Tr}_H(T).$$
--   No surjectivity of $U$ is assumed. The operators are right-projected operators on the ambient Hilbert spaces; the statement is not limited to their compressions.
--
--   For the proposed fixed-prime trace calculation, this is the structural cancellation of a common inner multiplier. Identifying the actual theta ranges with the indicated images, checking the intertwining relation, and proving nuclearity of the model operator are hypotheses to be established in that application.
-- source:
--   Auxiliary operator theorem for Yi's 'Actual global unit-shell increment at fixed incoming bandwidth', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-a91427c0-0f6d-4e33-aa30-fe6dd8cddd02, step 5 ('Trace on the actual limiting projections'). This is an explicit general Hilbert-space lemma supporting the proposed repair, rather than a formalization of the full global trace formula. The theorem isolates common-multiplier cancellation; no global Hardy/theta identification, cutoff order, or RH assertion is included.

import Definitions.Def_MasulloGRH_HilbertNuclear
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
set_option autoImplicit false
open MasulloGRH ContinuousLinearMap

theorem MasulloRepair.relative_projection_trace_isometry {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H →ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (B : K →L[ℂ] K)
    (P Q : Submodule ℂ H) [CompleteSpace P] [CompleteSpace Q]
    (hinter : ∀ v : H, B (U v) = U (A v))
    (hnuc : IsNuclearOperator (A ∘L (P.starProjection - Q.starProjection))) :
    let T := A ∘L (P.starProjection - Q.starProjection)
    let S := B ∘L ((P.map (U : H →ₗ[ℂ] K)).starProjection -
      (Q.map (U : H →ₗ[ℂ] K)).starProjection)
    S = U.toContinuousLinearMap ∘L T ∘L U.toContinuousLinearMap.adjoint ∧
      IsNuclearOperator S ∧ operatorTrace S = operatorTrace T := by sorry
