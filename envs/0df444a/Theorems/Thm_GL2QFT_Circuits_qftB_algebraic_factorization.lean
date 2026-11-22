-- Prove2me | Theorems.Thm_GL2QFT_Circuits_qftB_algebraic_factorization
-- name    : GL2QFT.Circuits.qftB_algebraic_factorization
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:38:35.755829+00:00
-- url     : https://prove2.me/theorems/2f35fa0f-9aca-401f-b02f-52d9b38ec20e
-- title:
--   Exact factorization of the Borel QFT $F_B$ into finite-field QFTs and $U_{B,\mathrm{transv}}$
-- statement:
--   In the subgroup-adapted Gelfand–Tsetlin bases of Theorem 6.13, the Fourier transform $F_B$ of the Borel subgroup $B = \{\bigl(\begin{smallmatrix} 1 & b \\ 0 & 1 \end{smallmatrix}\bigr)\bigl(\begin{smallmatrix} a & 0 \\ 0 & d \end{smallmatrix}\bigr)\}$ factors exactly as the three-register finite-field transform $\mathfrak{F}_\times \otimes \mathfrak{F}_\times \otimes (\mathfrak{F}_\times \log_g \mathfrak{F}_+)$ followed by the reversible basis relabeling $U_{B,\mathrm{transv}}$:
--
--   $$F_B = U_{B,\mathrm{transv}} \cdot \bigl(\mathfrak{F}_\times \otimes \mathfrak{F}_\times \otimes (\mathfrak{F}_\times \log_g \mathfrak{F}_+)\bigr)\big|_{\mathrm{submatrix}}.$$
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.2, eqs. (123)–(125) & Figure 13 (pp. 43–44)

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem qftB_algebraic_factorization (D : FieldData) : D.qftB = permMat (fbOutPerm D) * Matrix.submatrix (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) * frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) * frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D)) (bMidInj D) (bInEmb D) := by sorry

end Circuits
end GL2QFT
