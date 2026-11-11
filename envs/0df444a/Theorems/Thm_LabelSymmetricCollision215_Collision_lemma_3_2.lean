-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_3_2
-- name    : LabelSymmetricCollision215.Collision.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:44.097066+00:00
-- url     : https://prove2.me/theorems/659cefc5-d241-4f41-9bf7-720b30fd5511
-- title:
--   Lemma 3.2 — Compressed and standard states
-- statement:
--   For any $T$-query unitary algorithm and every checkpoint $0\le t\le T$, let $\psi_t$ be its purified state under the uniform input distribution and $\widetilde\psi_t$ its recording state, starting at the empty database. Then
--   $$\operatorname{Comp}\psi_t=\widetilde\psi_t.$$
--   This identifies the two oracle descriptions of the same computation.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 3.2, PDF 17 / printed 15

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 3.2, PDF 17 / printed 15. -/
theorem lemma_3_2 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (t : Fin (T+1)) :
    compress M N W (uniformJoint A t) = recordingState A t := by sorry

end LabelSymmetricCollision215.Collision
