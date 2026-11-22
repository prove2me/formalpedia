-- Prove2me | Theorems.Thm_GL2QFT_Circuits_stage_Mbr_uniform
-- name    : GL2QFT.Circuits.stage_Mbr_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:41.91828+00:00
-- url     : https://prove2.me/theorems/b7c4af46-9bae-4b4e-84e5-6a5b5f0dc70a
-- title:
--   Stage 4 of Theorem 6.34: uniform coherent branch transform $F_\times \oplus F_{\ker N}$
-- statement:
--   For $q > 2$, the canonical branch transform `canonMbrCore D γ` performing $\mathfrak{F}_\times$ on split branch states $|\mathrm{sp}, r\rangle$ ($r \in \mathbb{F}_q^\times$) and $F_{\ker N} \cong \mathrm{QFT}_{q+1}$ on nonsplit states $|\mathrm{ns}, r\rangle$ ($r \in \ker N$) is uniformly implemented from `gammaFq2BranchCode` to `branchPairCode`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.5, Definition 6.19 & Section 6.5.1–6.5.2 (pp. 50, 52–54)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem stage_Mbr_uniform : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => gammaFq2BranchCode D) (fun D => branchPairCode D) (fun D => Matrix.of fun (out : BranchPair D) (inp : D.Lab × BranchSrc D) => if h : out.1 = inp.1 then canonMbrCore D inp.1 (cast (congrArg (BranchOut D) h) out.2) inp.2 else 0) := by sorry

end Circuits
end GL2QFT
