-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_claim_4_9
-- name    : LabelSymmetricCollision215.Collision.claim_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:53.081585+00:00
-- url     : https://prove2.me/theorems/c9b671d0-9aec-4f51-85fd-85507888f19c
-- title:
--   Claim 4.9 — Arrangement graph kernel
-- statement:
--   For $s\ge1$, let $D$ be the deletion map and $A_{N,s}$ the independently defined arrangement adjacency operator on injective tuples. Then
--   $$\ker D=\ker(D^\dagger D)=\ker(A_{N,s}+s\operatorname{Id}).$$
--   Thus deletion detects the bottom adjacency eigenspace.
--
--   Differences from the source:
--   - encoding: collision-free subspace and deletion to s copies of the (s−1)-tuple space → Euclidean coordinates on injective tuples, with remaining positions indexed by the complement of the deleted position; reason: canonical orthonormal basis equivalences; the kernel in Claim 4.8 is explicitly embedded in the ambient tensor space
--   - generalization: stated inside the proof of Theorem 4.6, under its standing assumptions s ≥ 1 and N ≥ 2s → s ≥ 1 and every positive N (no hypothesis N ≥ 2s); reason: the deletion-map identities hold for every N; for N ≥ 2s the Lean statement is exactly the source claim
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Claim 4.9, PDF 25 / printed 23

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Claim 4.9, PDF 25 / printed 23. -/
theorem claim_4_9 (N s : ℕ) [NeZero N] (hs : 1 ≤ s) :
    (deletion N s).toLinearMap.ker =
      ((deletion N s).adjoint.comp (deletion N s)).toLinearMap.ker ∧
    ((deletion N s).adjoint.comp (deletion N s)).toLinearMap.ker =
      (arrangement N s + (s : ℂ) • ContinuousLinearMap.id ℂ _).toLinearMap.ker := by sorry

end LabelSymmetricCollision215.Collision
