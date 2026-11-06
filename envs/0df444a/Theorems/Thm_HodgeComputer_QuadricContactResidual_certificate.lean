-- Prove2me | Theorems.Thm_HodgeComputer_QuadricContactResidual_certificate
-- name    : HodgeComputer.QuadricContactResidual.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:03:02.88731+00:00
-- url     : https://prove2.me/theorems/1a4e61c6-9821-4e86-b11a-97592d859b6c
-- title:
--   Quadric contact · residual sector — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Quadric contact · residual sector”](https://hodge.computer/#case/quadric-contact-residual), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/quadric-contact-residual).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/quadric-contact-residual/instance.rec

import Definitions.Def_HodgeComputerQuadricContactResidual

theorem HodgeComputer.QuadricContactResidual.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.QuadricContactResidual.n)
      HodgeComputer.QuadricContactResidual.F
      HodgeComputer.QuadricContactResidual.A
      HodgeComputer.QuadricContactResidual.d
      HodgeComputer.QuadricContactResidual.q := by
  sorry
