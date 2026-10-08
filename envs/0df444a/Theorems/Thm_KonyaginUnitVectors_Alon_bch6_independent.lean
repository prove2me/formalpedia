-- Prove2me | Theorems.Thm_KonyaginUnitVectors_Alon_bch6_independent
-- name    : KonyaginUnitVectors.Alon.bch6_independent
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T14:10:19.662323+00:00
-- url     : https://prove2.me/theorems/a04f8f27-b0ce-4659-b2a2-d6fd43b94f2c
-- title:
--   Any six columns of the BCH check matrix of designed distance 7 are independent
-- statement:
--   Let $F$ be a field of characteristic $2$ and let $T\subseteq F\setminus\{0\}$ be a finite set with at most $6$ elements such that
--
--   $$\sum_{x\in T}x=\sum_{x\in T}x^{3}=\sum_{x\in T}x^{5}=0 .$$
--
--   Then $T=\varnothing$. Equivalently, any at most six distinct columns $(x,x^3,x^5)^{\top}$, $x\in F\setminus\{0\}$, of the parity-check matrix of the binary BCH code of designed distance $7$ are linearly independent over $\mathbb F_2$.
--
--   **Formalization Note.** Only the characteristic is assumed; $F$ need not be finite.
-- source:
--   N. Alon, Explicit Ramsey graphs and orthonormal labelings, Electron. J. Combin. 1 (1994), R12, doi:10.37236/1192 (Sections 3 and 4; the construction here partitions by Tr(x^9) instead of the leading bit of x^7)

import Mathlib

namespace KonyaginUnitVectors.Alon

theorem bch6_independent {F : Type*} [Field F] [CharP F 2] (T : Finset F) (h0 : (0 : F) ∉ T)
    (hT : T.card ≤ 6) (h1 : ∑ x ∈ T, x = 0) (h3 : ∑ x ∈ T, x ^ 3 = 0) (h5 : ∑ x ∈ T, x ^ 5 = 0) :
    T = ∅ := by sorry

end KonyaginUnitVectors.Alon
