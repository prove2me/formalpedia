-- Prove2me | Theorems.Thm_OracleStateHSP_eq_57
-- name    : OracleStateHSP.eq_57
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:46.014694+00:00
-- url     : https://prove2.me/theorems/fbaf9080-5de8-4055-b907-2d3e39e2b88c
-- title:
--   Eq. (57): $O^1_f = \left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right) \otimes O_f$
-- statement:
--   At $\varepsilon = 1$ the fractional oracle reduces to
--   $$
--   O^1_f = \begin{pmatrix} 0 & -O_f \\ O_f & 0 \end{pmatrix} = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix} \otimes O_f ,
--   $$
--   with the flag qubit as the first tensor factor and $O_f$ the Padded Simon oracle. Thus $O^1_f$ differs from $O_f$ only by a fixed one-qubit gate.
--
--   Differences from the source:
--   - generalization: f a Simon function → every f : Z_2^m → Z_2^m; reason: the identity is entrywise and uses no property of f
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (57), p.39

import Mathlib
import Definitions.Def_OracleStateHSP_fracOracle

namespace OracleStateHSP

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (57), p.39: at `ε = 1` the fractional oracle reduces to
`O^1_f = [ 0 , −O_f ; O_f , 0 ] = [ 0 , −1 ; 1 , 0 ] ⊗ O_f`, with the flag qubit as the outer
tensor factor.

**Formalization Note.** Stated for every `f : Z_2^m → Z_2^m`. -/
theorem eq_57 (r m : ℕ) (f : V m → V m) :
    fracOracle 1 r f = Matrix.kronecker !![0, -1; 1, 0] (paddedOracle r f) := by sorry

end OracleStateHSP
