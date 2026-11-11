-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_corollary_4_18
-- name    : LabelSymmetricCollision215.Collision.corollary_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:49.840314+00:00
-- url     : https://prove2.me/theorems/fe005a03-a62d-4dad-b854-bc459007112a
-- title:
--   Corollary 4.18 — Success bound with constants
-- statement:
--   Let $A$ be label-symmetric, with $T$ queries and algorithm dimension at most $2^S$, where $N\ge9$ and $S\ge\log_2N$. For any actual final collision-triple decoding,
--   $$p_{\rm succ}^{\mathcal U}\le\left(\frac{4T}{\sqrt N}\sqrt{\min\{T,2S/\log_2N\}}+\sqrt{2/N}\right)^2.$$
--   In addition, if $T\ge1$,
--   $$p_{\rm succ}^{\mathcal U}\le\frac{36T^2}N\min\{T,2S/\log_2N\}.$$
--   Both clauses concern the uniform distribution on all inputs, including injective inputs.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
--   - generalization: S qubits of algorithm space → real S with algorithm dimension at most 2^S; reason: the source uses only its displayed dimension charge, so every integer qubit budget is recovered by substitution
--   - encoding: A outputs a triple (x1, x2, y) via its final measurement → computational-basis measurement of the whole final algorithm register followed by an arbitrary decoding map out into triples or a failure symbol (none counts as failure); reason: any input-independent final change of basis is absorbed into U_T, and the output register is part of the charged algorithm space; same success probabilities
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Corollary 4.18, PDF 34 / printed 32

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Corollary 4.18, PDF 34 / printed 32. -/
theorem corollary_4_18 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (S : ℝ) (hspace : UsesSpace M N W S)
    (hN : 9 ≤ N) (hS : logTwo N ≤ S) (hsym : LabelSymmetric A) (out : Reg M N W → Output M N) :
    success A out ≤ (4*T/Real.sqrt N * Real.sqrt (min (T : ℝ) (2*S/logTwo N)) +
      Real.sqrt (2/(N : ℝ)))^2 ∧
    (1 ≤ T → success A out ≤ 36*(T : ℝ)^2/N * min (T : ℝ) (2*S/logTwo N)) := by sorry

end LabelSymmetricCollision215.Collision
