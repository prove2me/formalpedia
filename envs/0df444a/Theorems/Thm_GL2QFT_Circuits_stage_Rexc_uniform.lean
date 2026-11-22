-- Prove2me | Theorems.Thm_GL2QFT_Circuits_stage_Rexc_uniform
-- name    : GL2QFT.Circuits.stage_Rexc_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:31.968194+00:00
-- url     : https://prove2.me/theorems/1b07cb13-5ead-42f7-b699-96e331e17da9
-- title:
--   Stage 6 of Theorem 6.34: uniform coherent exceptional correction $R_{\mathrm{exc},\gamma}$
-- statement:
--   For $q > 2$, the exceptional $2\times 2$ correction $R_{\mathrm{exc},\gamma}$ acting on $(A_\gamma |c_\alpha\rangle, |\det_\alpha\rangle)$ for roots $2\alpha = \gamma$ (at most two solutions in $\mathbb{Z}/(q-1)\mathbb{Z}$) is uniformly implemented coherently in $\gamma$ from `gammaExtCode` to `gammaExtCode`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5, Definition 6.21 & eqs. (156)–(157) (pp. 50, 54–55)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem stage_Rexc_uniform : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => gammaExtCode D) (fun D => gammaExtCode D) (fun D => subMat (fun γ => Rexc D γ D.Irr)) := by sorry

end Circuits
end GL2QFT
