-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_claim_4_12
-- name    : LabelSymmetricCollision215.Collision.claim_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:52.970576+00:00
-- url     : https://prove2.me/theorems/7719737f-e994-4936-bfbd-b7da5a98023d
-- title:
--   Claim 4.12 — Orthogonal collision components
-- statement:
--   Assume $s\ge2$ and $N\ge2s$. For any tuple-space vector $u$, define
--   $$v=(\Pi_{W^{\otimes s}}\Pi_{C_s^\perp}-\Pi_{C_s^\perp\cap W^{\otimes s}})u,\quad z=\Pi_{C_s^\perp}v,\quad c=v-z.$$
--   Then
--   $$(N-2s+2)\|z\|^2\le(2s-2)\|c\|^2.$$
--   The components are constructed from the vector in the surrounding proof, rather than arbitrary parameters.
--
--   Differences from the source: none.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Claim 4.12, PDF 28 / printed 26

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Claim 4.12, PDF 28 / printed 26. -/
theorem claim_4_12 (N s : ℕ) [NeZero N] (hs : 2 ≤ s) (hN : 2*s ≤ N)
    (u : H (Tuple N s)) :
    let v := projectionError N s u
    let z := (freeTensor N s).starProjection v
    let c := v-z
    ((N : ℝ)-2*s+2) * ‖z‖^2 ≤ (2*(s : ℝ)-2) * ‖c‖^2 := by sorry

end LabelSymmetricCollision215.Collision
