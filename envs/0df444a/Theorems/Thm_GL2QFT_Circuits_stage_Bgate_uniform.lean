-- Prove2me | Theorems.Thm_GL2QFT_Circuits_stage_Bgate_uniform
-- name    : GL2QFT.Circuits.stage_Bgate_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:29.026265+00:00
-- url     : https://prove2.me/theorems/0b133ba4-16b1-47db-bd1d-dd8b5aa6f1c7
-- title:
--   Stage 3 of Theorem 6.34: uniform coherent quadratic branching transform $B_\gamma$
-- statement:
--   For $q > 2$, the quadratic branching isometry $B_\gamma$ solving $X^2 - X + t = 0$ over $\mathbb{F}_q$ or $\mathbb{F}_{q^2}$ is uniformly implemented (restricted to its image `BranchSrc D`) from `gammaFqCode` to `gammaFq2BranchCode`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5, Definition 6.18 & Section 6.5.2 (pp. 49, 52–54)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem stage_Bgate_uniform : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => gammaFqCode D) (fun D => gammaFq2BranchCode D) (fun D => subMat (BgateSub D)) := by sorry

end Circuits
end GL2QFT
