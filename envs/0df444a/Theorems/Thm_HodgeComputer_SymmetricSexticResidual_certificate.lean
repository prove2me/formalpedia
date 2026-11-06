-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_certificate
-- name    : HodgeComputer.SymmetricSexticResidual.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T21:39:54.14078+00:00
-- url     : https://prove2.me/theorems/799e785b-ddce-4562-b682-39cbf72890b9
-- title:
--   Permutation symmetry · residual sector — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Permutation symmetry · residual sector”](https://hodge.computer/#case/symmetric-sextic-residual), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/symmetric-sextic-residual).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/symmetric-sextic-residual/instance.rec

import Definitions.Def_HodgeComputerSymmetricSexticResidual

theorem HodgeComputer.SymmetricSexticResidual.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.SymmetricSexticResidual.n)
      HodgeComputer.SymmetricSexticResidual.F
      HodgeComputer.SymmetricSexticResidual.A
      HodgeComputer.SymmetricSexticResidual.d
      HodgeComputer.SymmetricSexticResidual.q := by
  sorry
