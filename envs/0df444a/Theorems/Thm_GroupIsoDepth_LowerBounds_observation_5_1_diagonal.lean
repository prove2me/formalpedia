-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_observation_5_1_diagonal
-- name    : GroupIsoDepth.LowerBounds.observation_5_1_diagonal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:41:15.193294+00:00
-- url     : https://prove2.me/theorems/e29f61e7-8b2d-44f2-9c94-c86f430fd1d0
-- title:
--   Observation 5.1, proof — $(T,T)$ is a yes-instance of GpI iff $T$ is a valid group table
-- statement:
--   For every multiplication table $T$ of order $n$ (every bit string of length $n^2\lceil\log_2 n\rceil$), the pair $(T,T)$ belongs to the total Group Isomorphism language $\mathrm{GpI}_n$ if and only if $T$ is a valid multiplication table of a group ($T\in\mathrm{VALID}_n$).
--
--   Differences from the source:
--   - encoding: each entry a ⌈log₂ n⌉-bit label of an element of [n] (bit order not fixed) → TableVar n = Fin n × Fin n × Fin (Nat.clog 2 n); entry = Σ_b x(i,j,b)·2^b (bit b has weight 2^b); labels [n] = Fin n = {0,…,n−1}; reason: any fixed bit order and label set is a renaming of the input variables; no instance and no size changes
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), proof of Observation 5.1 (p. 35, PDF 36)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables

namespace GroupIsoDepth.LowerBounds

/-- Proof of Observation 5.1 (printed p. 35, PDF 36): for every multiplication table `T` of order
`n` (every bit string of its `n²⌈log₂ n⌉` input bits), the pair `(T, T)` is a yes-instance of Group
Isomorphism if and only if `T` is a valid multiplication table of a group. -/
theorem observation_5_1_diagonal (n : ℕ) (x : TableVar n → Bool) :
    GpI n (diagPair x) ↔ ValidGroup n x := by sorry

end GroupIsoDepth.LowerBounds
