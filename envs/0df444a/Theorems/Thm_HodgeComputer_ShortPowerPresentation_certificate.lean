-- Prove2me | Theorems.Thm_HodgeComputer_ShortPowerPresentation_certificate
-- name    : HodgeComputer.ShortPowerPresentation.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:08:17.222214+00:00
-- url     : https://prove2.me/theorems/1d7a74dc-f59e-4005-838a-bc0bec8007a9
-- title:
--   Eight powers · linear-section remainder — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Eight powers · linear-section remainder”](https://hodge.computer/#case/short-power-presentation), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/short-power-presentation).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/short-power-presentation/instance.rec

import Definitions.Def_HodgeComputerShortPowerPresentation

theorem HodgeComputer.ShortPowerPresentation.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.ShortPowerPresentation.n)
      HodgeComputer.ShortPowerPresentation.F
      HodgeComputer.ShortPowerPresentation.A
      HodgeComputer.ShortPowerPresentation.d
      HodgeComputer.ShortPowerPresentation.q := by
  sorry
