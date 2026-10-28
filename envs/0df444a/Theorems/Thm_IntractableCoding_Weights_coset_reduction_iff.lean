-- Prove2me | Theorems.Thm_IntractableCoding_Weights_coset_reduction_iff
-- name    : IntractableCoding.Weights.coset_reduction_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:00.203916+00:00
-- url     : https://prove2.me/theorems/7662eb65-a5d9-495f-83fa-06d8c0c0b947
-- title:
--   Section III, p. 385 — the COSET WEIGHTS instance (B, 11⋯1, |T|) is a yes-instance iff the triples admit a matching
-- statement:
--   Let $U\subseteq T\times T\times T$ with $|T|=n$, and let $B$ be its triple incidence matrix. Then $U$ admits a matching if and only if the COSET WEIGHTS instance $(A,y,w)=(B,\ 11\cdots1,\ n)$ is a yes-instance:
--   $$U\text{ admits a matching}\iff\exists x\in\mathrm{GF}(2)^{|U|},\ |x|\le n\ \text{and}\ xB=11\cdots1.$$
--
--   Together with the polynomial-time computability of the map $U\mapsto(B,11\cdots1,n)$ this is the reduction of THREE-DIMENSIONAL MATCHING to COSET WEIGHTS. Note that COSET WEIGHTS asks for weight at most $n$ while a matching uses exactly $n$ rows.
--
--   Differences from the source:
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III, reduction of THREE-DIMENSIONAL MATCHING to COSET WEIGHTS

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- The COSET WEIGHTS instance `(B, 11⋯1, |T|)` built from a 3DM instance is a yes-instance
iff the 3DM instance has a matching. -/
theorem coset_reduction_iff (I : ThreeDMInstance) :
    ThreeDMYes I ↔ CosetWeightsYes (cosetOf3DM I) := by sorry

end IntractableCoding.Weights
