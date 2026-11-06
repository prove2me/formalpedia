-- Prove2me | Theorems.Thm_HodgeComputer_DenseRational_certificate
-- name    : HodgeComputer.DenseRational.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T21:46:50.923924+00:00
-- url     : https://prove2.me/theorems/ea81211f-1bfe-49e7-93a4-88b71143c744
-- title:
--   Dense rational · full coefficient support — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Dense rational · full coefficient support”](https://hodge.computer/#case/dense-rational), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/dense-rational).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/dense-rational/instance.rec

import Definitions.Def_HodgeComputerDenseRational

theorem HodgeComputer.DenseRational.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.DenseRational.n)
      HodgeComputer.DenseRational.F
      HodgeComputer.DenseRational.A
      HodgeComputer.DenseRational.d
      HodgeComputer.DenseRational.q := by
  sorry
