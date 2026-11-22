-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_routing_and_small_blocks
-- name    : GL2QFT.Circuits.totalA_routing_and_small_blocks
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T04:38:48.25083+00:00
-- url     : https://prove2.me/theorems/9154023d-7056-404e-bc81-2e9b36dd317a
-- title:
--   Uniform circuit implementation of `totalA` for $q = 2$ and routing + small blocks for $q > 2$
-- statement:
--   The total $A$-matrix `totalA D` in the Mackey circuit for $B < \mathrm{GL}_2(\mathbb{F}_q)$ satisfies:
--
--   1. When $q = 2$, `totalA D` is uniformly implemented directly from `inCodeA` to `outCodeA`.
--
--   2. Whenever $q > 2$, given any uniform implementation of the coherent hard block $A_\gamma$ from `gammaInCode` to `gammaIrrCode`, routing between one-/two-dimensional small blocks and the hard block yields a uniform implementation of `totalA D` from `inCodeA` to `outCodeA`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, Theorem 6.14 & eqs. (128)–(147) (pp. 45–48)

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_TotalA
import Definitions.Def_GL2QFT_AGamma

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem totalA_routing_and_small_blocks : UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun D => outCodeA D) (fun D => totalA D) ∧ (UniformlyImplementsOn (fun D => 2 < D.q) (fun D => D.gammaInCode) (fun D => D.gammaIrrCode) (fun D => Matrix.of fun out inp => if out.1 = inp.1 then D.AGamma inp.1 out.2 inp.2 else 0) → UniformlyImplementsOn (fun D => 2 < D.q) (fun D => inCodeA D) (fun D => outCodeA D) (fun D => totalA D)) := by sorry

end Circuits
end GL2QFT
