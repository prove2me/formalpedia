-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_3_4
-- name    : LabelSymmetricCollision215.Collision.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:44.532427+00:00
-- url     : https://prove2.me/theorems/b2b4567f-0b2f-4680-a190-204c2d3618b3
-- title:
--   Lemma 3.4 — At most t occupied cells
-- statement:
--   For every $T$-query algorithm, at each checkpoint $0\le t\le T$ the recording state has support only on databases with at most $t$ nonempty cells:
--   $$\widetilde\psi_t(\eta,d)\ne0\ \Longrightarrow\ |\operatorname{occ}(d)|\le t.$$
--   This is the occupancy constraint obtained from recording queries.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 3.4, PDF 18 / printed 16

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 3.4, PDF 18 / printed 16. -/
theorem lemma_3_4 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (t : Fin (T+1)) : SupportedAtMost t.val (recordingState A t) := by sorry

end LabelSymmetricCollision215.Collision
