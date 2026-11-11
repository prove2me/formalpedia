-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_theorem_4_6
-- name    : LabelSymmetricCollision215.Collision.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:56.014575+00:00
-- url     : https://prove2.me/theorems/a3f8e22f-3f95-45fb-8864-cc26793c0489
-- title:
--   Theorem 4.6 — Collision-free compressed Specht decomposition
-- statement:
--   Assume $s\ge1$ and $N\ge2s$. As complex representations of the range-label symmetric group,
--   $$C_s^\perp\cap W^{\otimes s}\cong\bigoplus_{\mu\vdash s}|\operatorname{SYT}(\mu)|S^{(N-s,\mu)}.$$
--   The multiplicities are actual standard-tableau sets and the factors are actual complex Specht modules. This describes all collision-free compressed tensor components.
--
--   Differences from the source:
--   - encoding: complex Specht modules and standard-tableau multiplicities → published Young left ideals and increasing bijective fillings, transported to cyclic range labels; reason: these are concrete realizations of the same representations and multiplicity sets; height caps exclude no partition of the specified size
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Theorem 4.6, PDF 24 / printed 22

import Definitions.Def_LabelSymmetricCollision215_Collision_Specht

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Theorem 4.6, PDF 24 / printed 22. -/
theorem theorem_4_6 (N s : ℕ) [NeZero N] (hs : 1 ≤ s) (hN : 2*s ≤ N) :
    TensorDecomposition hN (intersection N s) := by sorry

end LabelSymmetricCollision215.Collision
