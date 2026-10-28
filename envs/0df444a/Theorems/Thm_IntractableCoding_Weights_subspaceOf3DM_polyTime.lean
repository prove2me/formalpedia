-- Prove2me | Theorems.Thm_IntractableCoding_Weights_subspaceOf3DM_polyTime
-- name    : IntractableCoding.Weights.subspaceOf3DM_polyTime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:04.965289+00:00
-- url     : https://prove2.me/theorems/dc418c14-d0aa-4027-b723-6a3b915eeb5d
-- title:
--   Section III, p. 385 — the SUBSPACE WEIGHTS instance (A, 3n² + 4n) is computed from the triples in polynomial time
-- statement:
--   The map sending a THREE-DIMENSIONAL MATCHING instance $U\subseteq T\times T\times T$ ($|T|=n$, $|U|=t$) to the SUBSPACE WEIGHTS instance $(A,\ 3n^2+4n)$, with $A$ the $(3nt+3n+t)\times(3nt+3n)$ matrix built from the triple incidence matrix, is computed by a polynomial-time multi-stack Turing machine: from the binary encoding of $U$ it writes the binary encoding of $(A,3n^2+4n)$ in a number of steps bounded by a polynomial in the input length.
--
--   This is the "in polynomial time" half of the reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS; note $t\le n^3$, so $A$ has polynomially many entries.
--
--   Differences from the source:
--   - encoding: input a set U ⊆ T × T × T of triples over a finite set T → ThreeDMInstance = ⟨n, edge⟩ with T = Fin n and U = {(a,b,c) | edge a b c}; the triples listed lexicographically, the incidence columns in three blocks a, n + b, 2n + c; reason: any finite T is in bijection with Fin |T|; the row and column orders change no weight and no instance's answer
--   - encoding: the input is encoded into a binary string of length N → encodeCoset / encodeSubspace: row and column counts in unary, the entries of A (and y) bit by bit, w in binary with a self-delimiting marker code; reason: a fixed honest encoding is part of any precise NP statement; unary dimensions keep the certificate length (the number of rows) polynomial in the input length, binary w is the shorter (stricter) choice for membership and changes nothing for hardness, since the reductions output w = n and w = 3n² + 4n
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III, reduction of THREE-DIMENSIONAL MATCHING to SUBSPACE WEIGHTS ("we will find out in polynomial time whether the original set of triples has a matching")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Reductions

namespace IntractableCoding.Weights

open PricingWithTips

/-- The SUBSPACE WEIGHTS reduction map is computed by a polynomial-time TM2 machine from the
encoding of the 3DM instance to the encoding of the SUBSPACE WEIGHTS instance. -/
theorem subspaceOf3DM_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime encodeThreeDMInstance encodeSubspace
      subspaceOf3DM) := by sorry

end IntractableCoding.Weights
