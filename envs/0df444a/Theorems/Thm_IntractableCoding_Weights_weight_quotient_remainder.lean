-- Prove2me | Theorems.Thm_IntractableCoding_Weights_weight_quotient_remainder
-- name    : IntractableCoding.Weights.weight_quotient_remainder
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:50.866525+00:00
-- url     : https://prove2.me/theorems/4c6fc290-bb45-4869-b3cc-0023c7c7fefa
-- title:
--   Section III, p. 385 — |x₀| and |y| are determined by |x|; |x| = 3n² + 4n gives |x₀| = n, |y| = 3n (corrected: |x₀| is the quotient and |y| the remainder)
-- statement:
--   In the setting of the weight identity ($xA=0$, $x_0$ the first $t$ components of $x$, $y=x_0B$, $n=|T|$):
--
--   1. $0\le|y|\le 3n$;
--   2. $|x_0|$ is the quotient and $|y|$ the remainder of $|x|$ divided by $3n+1$:
--   $$|x_0|=\left\lfloor\frac{|x|}{3n+1}\right\rfloor,\qquad |y|=|x|\bmod(3n+1);$$
--   3. in particular, if $|x|=3n^2+4n$ then $|x_0|=n$ and $|y|=3n$.
--
--   So $|x_0|$ and $|y|$ are uniquely determined by $|x|$; this is what turns a word of weight $3n^2+4n$ into $n$ rows of $B$ summing to $11\cdots1$.
--
--   Differences from the source:
--   - correction: |x₀| and |y| are the remainder and quotient (in that order) when |x| is divided by 3n + 1 → |x₀| = |x| / (3n + 1) (quotient) and |y| = |x| % (3n + 1) (remainder); reason: the printed order is false: n = 1, U = {(1,1,1)}, x = all ones (t = 1) has xA = 0, |x₀| = 1, |y| = 3, |x| = 7 = 1·4 + 3, so the remainder 3 ≠ |x₀| and the quotient 1 ≠ |y|; the paper's next sentence (|x| = 3n² + 4n gives |x₀| = n, |y| = 3n) uses the correct order
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III, reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS ("Since 0 ≤ |y| ≤ 3n, …")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- For every `x` with `xA = 0` (`A = subspaceMatrix I`, `n = |T|`), with `x₀ = firstPart I x`
and `y = x₀ B`: `|y| ≤ 3n`, `|x₀|` is the quotient and `|y|` the remainder of `|x|` divided by
`3n + 1`, and if `|x| = 3n² + 4n` then `|x₀| = n` and `|y| = 3n`. -/
theorem weight_quotient_remainder (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) ≤ 3 * I.1 ∧
      hammingNorm (firstPart I x) = hammingNorm x / (3 * I.1 + 1) ∧
      hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = hammingNorm x % (3 * I.1 + 1) ∧
      (hammingNorm x = 3 * I.1 ^ 2 + 4 * I.1 →
        hammingNorm (firstPart I x) = I.1 ∧
          hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) = 3 * I.1) := by sorry

end IntractableCoding.Weights
