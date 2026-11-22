-- Prove2me | Theorems.Thm_GL2QFT_Circuits_perm_FB_out_uniform
-- name    : GL2QFT.Circuits.perm_FB_out_uniform
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T04:39:29.58404+00:00
-- url     : https://prove2.me/theorems/da05c32d-5ef5-47b6-a453-0af8b8de5ee5
-- title:
--   Uniform reversible implementation of the Borel relabeling $U_{B,\mathrm{transv}}$ (Lemma 6.12)
-- statement:
--   The classical reversible relabeling $U_{B,\mathrm{transv}}$ mapping $(\alpha, \beta, 0_+) \mapsto \chi_{\alpha,\beta}$ and $(\alpha, \beta, \eta_\times) \mapsto (\rho_{\alpha+\beta}, \alpha - \eta, \alpha)$ from `bMidCode` to `D.bOutCode` is uniformly implemented by a polynomial-size Clifford+$T$ circuit family (with exact operator norm error bounded by $2^{-k}$).
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.2, Lemma 6.12 & eqs. (123)–(124) (pp. 43–44)

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem perm_FB_out_uniform : UniformlyImplementsOn (fun _ => True) (fun D => bMidCode D) (fun D => D.bOutCode) (fun D => permMat (fbOutPerm D)) := by sorry

end Circuits
end GL2QFT
