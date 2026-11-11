-- Prove2me | Theorems.Thm_NuclearTensor_Membership_projective_bridge
-- name    : NuclearTensor.Membership.projective_bridge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:15:45.40123+00:00
-- url     : https://prove2.me/theorems/aebc8317-fbea-4597-8af9-e27bfaf452d4
-- title:
--   Coordinate bridge for the real nuclear infimum
-- statement:
--   Let $d,k>0$ and let $M$ be any real order-$k$ tensor with local dimension $d$. Its finite signed unit-factor decomposition domain is nonempty, and its source nuclear norm equals Mathlib's projective seminorm of its ordinary algebraic coordinate realization:
--   $$\|M\|_* = \|\mathcal T(M)\|_\pi.$$
--   This infrastructure target identifies two infima over finite decompositions. It does not identify either with the Frobenius norm. Its explicit nonemptiness conclusion guards the source infimum on every input and supplies a reusable bridge to the installed tensor library.
--
--   Differences from the source:
--
--   - encoding: all real tensors with positive d and k → all row-major Euclidean arrays for d,k>0, including d=1 and k=1; reason: this is the same full source tensor space, with no restriction on entries or rank
--   - encoding: the real signed finite-decomposition nuclear infimum → the complete-lattice nonnegative extended-real nuclear infimum; reason: it has the same finite value in every source dimension; an empty domain would have value infinity rather than a real default of zero
--   - encoding: the source nuclear decomposition infimum → equality with Mathlib projectiveSeminorm after standard tensor-basis coordinate realization; reason: both range over all finite real tensor decompositions; normalizing nonzero factors gives the source signed unit-factor costs
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.21, Section 5.1.1 nuclear-norm definition; Mathlib PiTensorProduct.projectiveSeminorm

import Definitions.Def_NuclearTensor_Membership_ProjectiveBridge

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct ENNReal

namespace NuclearTensor.Membership

/-- Bridge to the installed Mathlib infimum, rather than identifying its norm with Frobenius. -/
theorem projective_bridge (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (M : Tensor (List.replicate k d)) :
    (decompositionCosts M).Nonempty ∧
    nuclearNorm M = ENNReal.ofReal (PiTensorProduct.projectiveSeminorm (coordinateTensor d k M)) := by sorry

end NuclearTensor.Membership
