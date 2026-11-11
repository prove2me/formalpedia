-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_4_17
-- name    : LabelSymmetricCollision215.Collision.lemma_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:47.507199+00:00
-- url     : https://prove2.me/theorems/d4fb1952-ba7c-43ff-b3b2-508e937f19bc
-- title:
--   Lemma 4.17 — Cumulative collision progress
-- statement:
--   Let $A$ be a label-symmetric $T$-query unitary algorithm with algorithm dimension at most $2^S$, where $N\ge9$ and $S\ge\log_2N$. For every nonnegative query count $T$,
--   $$\Delta_T\le\frac{4T}{\sqrt N}\sqrt{\min\{T,2S/\log_2N\}}.$$
--   There is no upper restriction on $T$. This is the cumulative recording-progress estimate.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
--   - generalization: S qubits of algorithm space → real S with algorithm dimension at most 2^S; reason: the source uses only its displayed dimension charge, so every integer qubit budget is recovered by substitution
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 4.17, PDF 33 / printed 31

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 4.17, PDF 33 / printed 31. -/
theorem lemma_4_17 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (S : ℝ) (hspace : UsesSpace M N W S)
    (hN : 9 ≤ N) (hS : logTwo N ≤ S) (hsym : LabelSymmetric A) :
    progress A (Fin.last T) ≤ 4*T/Real.sqrt N * Real.sqrt (min (T : ℝ) (2*S/logTwo N)) := by sorry

end LabelSymmetricCollision215.Collision
