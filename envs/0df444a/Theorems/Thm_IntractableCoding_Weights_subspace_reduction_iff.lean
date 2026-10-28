-- Prove2me | Theorems.Thm_IntractableCoding_Weights_subspace_reduction_iff
-- name    : IntractableCoding.Weights.subspace_reduction_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:58.689617+00:00
-- url     : https://prove2.me/theorems/609a14a5-820b-4bd8-8f03-fc9b16589d11
-- title:
--   Section III, pp. 385–386 — the code with parity-check matrix A has a word of weight 3n² + 4n iff the triples admit a matching
-- statement:
--   Let $U\subseteq T\times T\times T$ with $|T|=n$ and $|U|=t$, and let $A$ be the $(3nt+3n+t)\times(3nt+3n)$ matrix built from the triple incidence matrix $B$ (top $t$ rows $B$ followed by $3n$ copies of $I_t$; lower rows the identity $I_{3n(t+1)}$). Then
--   $$U\text{ admits a matching}\iff\exists x\in\mathrm{GF}(2)^{3nt+3n+t},\ |x|=3n^2+4n\ \text{and}\ xA=0,$$
--   that is, the SUBSPACE WEIGHTS instance $(A,\ 3n^2+4n)$ is a yes-instance exactly when $U$ admits a matching.
--
--   Together with the polynomial-time computability of $U\mapsto(A,3n^2+4n)$ this is the reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS.
--
--   Differences from the source:
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, pp. 385–386, Section III, reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- The code with parity-check matrix `A = subspaceMatrix I` has a word of weight
`3n² + 4n` iff the set of triples admits a matching. -/
theorem subspace_reduction_iff (I : ThreeDMInstance) :
    ThreeDMYes I ↔ SubspaceWeightsYes (subspaceOf3DM I) := by sorry

end IntractableCoding.Weights
