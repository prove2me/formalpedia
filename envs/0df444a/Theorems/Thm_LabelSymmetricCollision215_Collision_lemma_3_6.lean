-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_3_6
-- name    : LabelSymmetricCollision215.Collision.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:42.031616+00:00
-- url     : https://prove2.me/theorems/55a01655-e049-43e8-b724-13820149ab98
-- title:
--   Lemma 3.6 — Actual success from recording progress
-- statement:
--   For any $T$-query algorithm and any final computational-basis decoding into collision triples or failure, let $p_{\rm succ}^{\mathcal U}$ be its actual success probability under uniform input, and let $\Delta_T=\|\Pi_{\ge1}\widetilde\psi_T\|$. Then
--   $$p_{\rm succ}^{\mathcal U}\le\left(\Delta_T+\sqrt{2/N}\right)^2.$$
--   This connects measured output success to the recording state.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
--   - encoding: A outputs a triple (x1, x2, y) via its final measurement → computational-basis measurement of the whole final algorithm register followed by an arbitrary decoding map out into triples or a failure symbol (none counts as failure); reason: any input-independent final change of basis is absorbed into U_T, and the output register is part of the charged algorithm space; same success probabilities
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 3.6, PDF 20 / printed 18

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 3.6, PDF 20 / printed 18. -/
theorem lemma_3_6 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (out : Reg M N W → Output M N) :
    success A out ≤ (progress A (Fin.last T) + Real.sqrt (2 / (N : ℝ)))^2 := by sorry

end LabelSymmetricCollision215.Collision
