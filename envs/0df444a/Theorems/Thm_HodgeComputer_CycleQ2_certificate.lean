-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_certificate
-- name    : HodgeComputer.CycleQ2.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T21:37:35.681505+00:00
-- url     : https://prove2.me/theorems/7b27688f-7333-4ba0-bdb7-5018424f042a
-- title:
--   Cyclic coupling · pole order two — certificate
-- statement:
--   For $q=2$, and the fixed $(F,A)$ of [“Cyclic coupling · pole order two”](https://hodge.computer/#case/cycle-q2), prove the existence of a rational vector field $v$ with components homogeneous of degree $7$ and common denominator relatively prime to $F$, satisfying $F^{3}\mid A-2\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/cycle-q2).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cycle-q2/instance.rec

import Definitions.Def_HodgeComputerCycleQ2

theorem HodgeComputer.CycleQ2.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.CycleQ2.n)
      HodgeComputer.CycleQ2.F
      HodgeComputer.CycleQ2.A
      HodgeComputer.CycleQ2.d
      HodgeComputer.CycleQ2.q := by
  sorry
