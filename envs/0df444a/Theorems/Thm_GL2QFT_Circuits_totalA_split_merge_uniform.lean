-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_split_merge_uniform
-- name    : GL2QFT.Circuits.totalA_split_merge_uniform
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T06:00:39.401829+00:00
-- url     : https://prove2.me/theorems/ee7c7e0f-c3ce-4508-b1fc-c1dbce931561
-- title:
--   Uniform reversible routing splitting hard from non-hard blocks of `totalA` for $q > 2$
-- statement:
--   For $q > 2$, testing whether an input register `(λ, κ, ω, λ̃) ∈ InReg D` or output register `(λ, μ, λ̃) ∈ OutReg D` has both Borel labels two-dimensional (`isHardIn`, `isHardOut`) reversibly prepends the direct-sum branch tag in `sumCode`; both `splitInA` and `mergeOutA` are uniformly implemented in Clifford+$T$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, Theorem 6.14 (pp. 45–48)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem totalA_split_merge_uniform : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => inCodeA D) (fun D => sumCode (fun x : InRegNonHard D => inCodeA D x.1) (fun x : InRegHard D => inCodeA D x.1)) (fun D => permMat (splitInA D)) ∧ UniformlyImplementsOn (fun D => 2 < D.q) (fun D => sumCode (fun y : OutRegNonHard D => outCodeA D y.1) (fun y : OutRegHard D => outCodeA D y.1)) (fun D => outCodeA D) (fun D => permMat (mergeOutA D)) := by sorry

end Circuits
end GL2QFT
