-- Prove2me | Theorems.Thm_HodgeComputer_OffPaired_certificate
-- name    : HodgeComputer.OffPaired.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:02:04.603206+00:00
-- url     : https://prove2.me/theorems/2690f31b-5e97-46f4-99c6-46d44a444273
-- title:
--   Broken paired signs — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Broken paired signs”](https://hodge.computer/#case/off-paired), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/off-paired).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/off-paired/instance.rec

import Definitions.Def_HodgeComputerOffPaired

theorem HodgeComputer.OffPaired.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.OffPaired.n)
      HodgeComputer.OffPaired.F
      HodgeComputer.OffPaired.A
      HodgeComputer.OffPaired.d
      HodgeComputer.OffPaired.q := by
  sorry
