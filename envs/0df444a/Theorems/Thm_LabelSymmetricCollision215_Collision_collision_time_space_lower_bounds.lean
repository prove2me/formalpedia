-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_collision_time_space_lower_bounds
-- name    : LabelSymmetricCollision215.Collision.collision_time_space_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:55.032557+00:00
-- url     : https://prove2.me/theorems/3d3c462d-ebeb-4db5-b851-11f426b40fdc
-- title:
--   Theorem 4.19 — Query and space lower bounds
-- statement:
--   Let $M,N$ be arbitrary positive integers with $N\ge9$. Consider a label-symmetric unitary quantum query algorithm with $T$ queries and algorithm dimension at most $2^S$, counting work, query, retained-information and output registers. If its actual final measurement and decoding output a triple $x_1<x_2$, $f(x_1)=f(x_2)=y$ with probability at least $2/3$, averaged over the uniform distribution on every function $f:[M]\to[N]$, then
--   $$T^3\ge\frac N{54},\qquad T^2S\ge\frac{N\log_2N}{108}.$$
--   These are the explicit inequalities derived in the proof of Theorem 4.19. They imply both printed asymptotic bounds with universal constants. The result concerns the specified unitary label-symmetric class. Neither a square domain nor a binary range encoding is assumed.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
--   - generalization: S qubits of algorithm space → real S with algorithm dimension at most 2^S; reason: the source uses only its displayed dimension charge, so every integer qubit budget is recovered by substitution
--   - generalization: T = Ω(N^(1/3)) and T²S = Ω(N log N) → T³ ≥ N/54 and T²S ≥ N log₂N/108 for every N ≥ 9; reason: these explicit uniform constants are established in the proof on PDF 35 / printed 33 and imply both printed conclusions
--   - encoding: A outputs a triple (x1, x2, y) via its final measurement → computational-basis measurement of the whole final algorithm register followed by an arbitrary decoding map out into triples or a failure symbol (none counts as failure); reason: any input-independent final change of basis is absorbed into U_T, and the output register is part of the charged algorithm space; same success probabilities
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Theorem 4.19, PDF 34 / printed 32; explicit constants in proof, PDF 35 / printed 33

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Theorem 4.19, PDF 34 / printed 32. Explicit constants: proof PDF 35 / printed 33. -/
theorem collision_time_space_lower_bounds {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (S : ℝ) (hspace : UsesSpace M N W S)
    (hN : 9 ≤ N) (hsym : LabelSymmetric A) (out : Reg M N W → Output M N)
    (hsuccess : (2 : ℝ)/3 ≤ success A out) :
    (N : ℝ)/54 ≤ (T : ℝ)^3 ∧ (N : ℝ)*logTwo N/108 ≤ (T : ℝ)^2*S := by sorry

end LabelSymmetricCollision215.Collision
