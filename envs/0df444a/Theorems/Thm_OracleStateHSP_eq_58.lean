-- Prove2me | Theorems.Thm_OracleStateHSP_eq_58
-- name    : OracleStateHSP.eq_58
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:31:50.982085+00:00
-- url     : https://prove2.me/theorems/763e497d-588f-4797-a31d-1b423f3a3580
-- title:
--   Eq. (58): $O^\varepsilon_f - O^\varepsilon_g = \sqrt\varepsilon\,(O^1_f - O^1_g)$
-- statement:
--   For $\varepsilon \in (0, 1]$ and any two functions $f, g$, the diagonal blocks cancel in the oracle difference:
--   $$
--   O^\varepsilon_f - O^\varepsilon_g = \sqrt{\varepsilon} \begin{pmatrix} 0 & -(O_f - O_g) \\ O_f - O_g & 0 \end{pmatrix} = \sqrt{\varepsilon}\,\bigl(O^1_f - O^1_g\bigr).
--   $$
--
--   This identity, combined with Fact 4.5, produces the factor $1/\sqrt\varepsilon$ in the lower bound.
--
--   **Formalization Note** The middle block matrix is written as $\bigl(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\bigr) \otimes (O_f - O_g)$, flag first.
--
--   Differences from the source:
--   - generalization: f, g Simon functions → every f, g : Z_2^m → Z_2^m; reason: the identity is entrywise and uses no property of f, g
--   - encoding: block matrix [0, −(O_f − O_g); O_f − O_g, 0] → the Kronecker product [0, −1; 1, 0] ⊗ (O_f − O_g); reason: the two matrices are equal entrywise
--   - encoding: G = Z_2^n with n = r + m → the product (Fin r → ZMod 2) × (Fin m → ZMod 2); reason: Z_2^n ≅ Z_2^r ⊕ Z_2^m as groups; the paper writes G = K ⊕ V itself
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (58), p.40

import Mathlib
import Definitions.Def_OracleStateHSP_fracOracle

namespace OracleStateHSP

/-- Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (58), p.40: for any two Simon functions `f, g` the diagonal blocks cancel in the
oracle difference, giving
`O^ε_f − O^ε_g = √ε [ 0 , −(O_f − O_g) ; O_f − O_g , 0 ] = √ε (O^1_f − O^1_g)`.

**Formalization Note.** The middle block matrix is written as `[ 0 , −1 ; 1 , 0 ] ⊗ (O_f − O_g)`
(flag outer). Stated for every `f, g : Z_2^m → Z_2^m` and `ε ∈ (0, 1]`. -/
theorem eq_58 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (r m : ℕ) (f g : V m → V m) :
    fracOracle ε r f - fracOracle ε r g =
        (Real.sqrt ε : ℂ) • Matrix.kronecker !![0, -1; 1, 0] (paddedOracle r f - paddedOracle r g) ∧
    fracOracle ε r f - fracOracle ε r g =
        (Real.sqrt ε : ℂ) • (fracOracle 1 r f - fracOracle 1 r g) := by sorry

end OracleStateHSP
