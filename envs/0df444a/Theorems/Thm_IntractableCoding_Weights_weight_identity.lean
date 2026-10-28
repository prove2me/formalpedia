-- Prove2me | Theorems.Thm_IntractableCoding_Weights_weight_identity
-- name    : IntractableCoding.Weights.weight_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:57.304015+00:00
-- url     : https://prove2.me/theorems/8bfa54ae-aca6-4220-b08b-acf11ca9c4c4
-- title:
--   Section III, p. 385 — every x with xA = 0 has |x₁| = |y| + 3n|x₀| and |x| = |y| + (3n + 1)|x₀|
-- statement:
--   Let $U\subseteq T\times T\times T$ with $|T|=n$ and $|U|=t$, let $B$ be its triple incidence matrix and $A$ the $(3nt+3n+t)\times(3nt+3n)$ SUBSPACE WEIGHTS matrix built from $B$. Let $x\in\mathrm{GF}(2)^{3nt+3n+t}$ satisfy $xA=0$, let $x_0$ be the vector of its first $t$ components, $x_1$ the vector of its last $3n(t+1)$ components, and $y=x_0B$. Then
--   $$|x_1|=|y|+3n|x_0|\qquad\text{and}\qquad |x|=|y|+(3n+1)|x_0|,$$
--   where $|\cdot|$ is the Hamming weight.
--
--   Differences from the source:
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III, reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- For every `x` with `xA = 0` (`A = subspaceMatrix I`), with `x₀ = firstPart I x`,
`x₁ = lastPart I x` and `y = x₀ B`: `|x₁| = |y| + 3n|x₀|` and `|x| = |y| + (3n + 1)|x₀|`. -/
theorem weight_identity (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2)
    (hx : Matrix.vecMul x (subspaceMatrix I) = 0) :
    hammingNorm (lastPart I x) =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          3 * I.1 * hammingNorm (firstPart I x) ∧
      hammingNorm x =
        hammingNorm (Matrix.vecMul (firstPart I x) (incidence I)) +
          (3 * I.1 + 1) * hammingNorm (firstPart I x) := by sorry

end IntractableCoding.Weights
