-- Prove2me | Theorems.Thm_NuclearTensor_Membership_nuclear_ball_identity
-- name    : NuclearTensor.Membership.nuclear_ball_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:22.111619+00:00
-- url     : https://prove2.me/theorems/f01832ef-7078-434b-a004-0864d4726b51
-- title:
--   Section 5.1.1 — nuclear unit ball equals the convex product hull
-- statement:
--   For every positive local dimension $d$ and positive order $k$, let $K^*$ be the unit ball of the real nuclear norm defined by arbitrary finite signed decompositions into unit-sphere factors. Then
--   $$K^*=\operatorname{conv}\{x_1\otimes\cdots\otimes x_k:x_j\in B_{\mathbb R^d}\}.$$
--   This is the ordinary convex hull of closed-unit-ball product vectors, not a closed-convex-hull definition of the nuclear ball. The identity connects the separately defined source infimum to the general weak-membership theorem.
--
--   Differences from the source:
--
--   - encoding: all real tensors with positive d and k → all row-major Euclidean arrays for d,k>0, including d=1 and k=1; reason: this is the same full source tensor space, with no restriction on entries or rank
--   - encoding: the real signed finite-decomposition nuclear infimum → the complete-lattice nonnegative extended-real nuclear infimum; reason: it has the same finite value in every source dimension; an empty domain would have value infinity rather than a real default of zero
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.21, Section 5.1.1, unnumbered first proof display

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem nuclear_ball_identity (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    nuclearBall (List.replicate k d) =
      productHull (fun j => unitBall ((List.replicate k d).getD j 0)) := by sorry

end NuclearTensor.Membership
