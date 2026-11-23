-- Prove2me | Theorems.Thm_GL2QFT_Circuits_nonHardLocal_uniform
-- name    : GL2QFT.Circuits.nonHardLocal_uniform
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:02:23.085371+00:00
-- url     : https://prove2.me/theorems/509a3c32-d93f-4fd1-ac97-13c00805c719
-- title:
--   Uniform coherent implementation of the non-hard closed-form local gates
-- statement:
--   For $q>2$, one uniform Clifford+$T$ circuit family implements the coherent direct sum of the non-hard local two-level matrices. Controlled by the retained source label, it applies the determinant–Steinberg rotation, a character sign, the mixed-block phase $\zeta_{\alpha,\beta}$, or the identity, on the clean two-level register. The circuit acts on the ten-field source code followed by the clean local wire, with operator-norm error $2^{-k}$ and polynomial size in $\log q$ and $k$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, arXiv:2608.28573, §6.4.4, equations (127)–(139), and the small-block implementation statement on p.46 (PDF p.47); Theorem 6.10 and Theorem 6.14, p.47 (PDF p.48).

import Definitions.Def_GL2QFT_Circuits_NonHardStages

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem GL2QFT.Circuits.nonHardLocal_uniform : UniformlyImplementsOn (fun D => 2 < D.q)
    (fun D => nonHardMidCode D) (fun D => nonHardMidCode D)
    (fun D => nonHardLocal D) := by sorry
