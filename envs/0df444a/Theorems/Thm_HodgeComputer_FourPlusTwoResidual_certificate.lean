-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_certificate
-- name    : HodgeComputer.FourPlusTwoResidual.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:02:46.477469+00:00
-- url     : https://prove2.me/theorems/a2e2bf50-dad9-4802-a2ec-9e0cdde364be
-- title:
--   Four plus two · suspension remainder — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Four plus two · suspension remainder”](https://hodge.computer/#case/four-plus-two-residual), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/four-plus-two-residual).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/four-plus-two-residual/instance.rec

import Definitions.Def_HodgeComputerFourPlusTwoResidual

theorem HodgeComputer.FourPlusTwoResidual.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.FourPlusTwoResidual.n)
      HodgeComputer.FourPlusTwoResidual.F
      HodgeComputer.FourPlusTwoResidual.A
      HodgeComputer.FourPlusTwoResidual.d
      HodgeComputer.FourPlusTwoResidual.q := by
  sorry
