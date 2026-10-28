-- Prove2me | Theorems.Thm_IntractableCoding_Weights_matching_iff_rows_sum_ones
-- name    : IntractableCoding.Weights.matching_iff_rows_sum_ones
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:03.846985+00:00
-- url     : https://prove2.me/theorems/a1d291c8-e9c5-4da5-8d2d-59c09df2a19a
-- title:
--   Section III, p. 385 — a matching is the existence of |T| rows of the incidence matrix whose mod 2 sum is 11⋯1
-- statement:
--   Let $U\subseteq T\times T\times T$ with $|T|=n$, and let $B$ be its $|U|\times 3n$ triple incidence matrix. Then $U$ contains a matching — a set $W\subseteq U$ with $|W|=|T|$ in which no two triples agree in any coordinate — if and only if there is $x\in\mathrm{GF}(2)^{|U|}$ with
--   $$|x|=n\qquad\text{and}\qquad xB=(11\cdots1)\pmod 2,$$
--   that is, if and only if some $|T|$ rows of $B$ have mod 2 sum $11\cdots1$ (the rows chosen are the support of $x$).
--
--   This restates THREE-DIMENSIONAL MATCHING in linear-algebraic terms and is the basis of both reductions.
--
--   Differences from the source:
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: binary matrix A, row vector x, xA computed mod 2 → Matrix (Fin m) (Fin n) (ZMod 2), Matrix.vecMul x A, Hamming weight hammingNorm; reason: GF(2) = ZMod 2; xA with x indexed by the rows is Matrix.vecMul
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III ("In terms of this matrix, a solution to the THREE-DIMENSIONAL MATCHING problem is the existence of |T| rows whose mod 2 sum is 111⋯1111.")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- A 3DM instance has a matching iff some `|T|` rows of its triple incidence matrix have
mod 2 sum `11⋯1`: the chosen rows are the support of a 0/1 row vector `x` of weight `|T|`. -/
theorem matching_iff_rows_sum_ones (I : ThreeDMInstance) :
    ThreeDMYes I ↔ ∃ x : Fin (tCount I) → ZMod 2,
      hammingNorm x = I.1 ∧ Matrix.vecMul x (incidence I) = fun _ => 1 := by sorry

end IntractableCoding.Weights
