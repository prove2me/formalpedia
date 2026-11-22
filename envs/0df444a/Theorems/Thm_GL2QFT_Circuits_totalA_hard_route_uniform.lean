-- Prove2me | Theorems.Thm_GL2QFT_Circuits_totalA_hard_route_uniform
-- name    : GL2QFT.Circuits.totalA_hard_route_uniform
-- status  : Open
-- author  : @dmitry
-- created : 2026-11-22T06:00:39.895155+00:00
-- url     : https://prove2.me/theorems/34aaee8c-8dea-453c-b1e2-c3ec3e734668
-- title:
--   Uniform reduction of the hard block of `totalA` ($q > 2$) to a coherent $A_\gamma$ oracle
-- statement:
--   For $q > 2$, every input $x = (\rho_\gamma, \kappa, \omega, \rho_{\tilde{\gamma}}) \in \mathrm{InRegHard}(D)$ forces $\tilde{\gamma} = \gamma$ and embeds reversibly into `(γ, c) ∈ Lab × Option Lab` (`gammaInCode`), while every hard output embeds reversibly into `(γ, μ)` (`gammaIrrCode`). By `A70_eq_AGamma`, any uniform implementation of $A_\gamma$ yields a uniform implementation of the hard submatrix of `totalA D`.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols (2026), Quantum Fourier transform toolbox, arXiv:2608.28573, §6.4.4, Theorem 6.14 & eqs. (143)–(145) (pp. 46–48)

import Definitions.Def_GL2QFT_Circuits_Leaves

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT
namespace Circuits

theorem totalA_hard_route_uniform (hAG : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => D.gammaInCode) (fun D => D.gammaIrrCode) (fun D => Matrix.of fun out inp => if out.1 = inp.1 then D.AGamma inp.1 out.2 inp.2 else 0)) : UniformlyImplementsOn (fun D => 2 < D.q) (fun D (x : InRegHard D) => inCodeA D x.1) (fun D (y : OutRegHard D) => outCodeA D y.1) (fun D => (totalA D).submatrix Subtype.val Subtype.val) := by sorry

end Circuits
end GL2QFT
