-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_nonhard_uniform
-- name    : GL2QFT.Circuits.totalA_nonhard_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:46.721477+00:00
-- url     : https://prove2.me/theorems/52550b49-d89f-4639-b217-21332e35333c
-- title:
--   Uniform circuit implementation of all non-hard ($1\times 1$ and $2\times 2$) blocks of `totalA`
-- statement:
--   For $q > 2$, on inputs `InRegNonHard D` (where at least one of $\lambda, \tilde{\lambda}$ is one-dimensional), every nonvanishing block of `totalA D` has dimension $1 \times 1$ or $2 \times 2$ with closed-form entries given by equations (128)–(139); hence the restricted non-hard block is uniformly implemented in Clifford+$T$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, Theorem 6.14 & eqs. (128)–(139) (pp. 45–47)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem totalA_nonhard_uniform : UniformlyImplementsOn (fun D => 2 < D.q) (fun D (x : InRegNonHard D) => inCodeA D x.1) (fun D (y : OutRegNonHard D) => outCodeA D y.1) (fun D => (totalA D).submatrix Subtype.val Subtype.val) := by sorry

end Circuits
end GL2QFT
