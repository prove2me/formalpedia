-- Prove2me | Theorems.Thm_HodgeComputer_CyclicTripleResidual_certificate
-- name    : HodgeComputer.CyclicTripleResidual.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:05:29.798807+00:00
-- url     : https://prove2.me/theorems/3f5a07ea-4764-4a6d-b075-c4efc68383a4
-- title:
--   Cyclic triple cover · complementary character — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Cyclic triple cover · complementary character”](https://hodge.computer/#case/cyclic-triple-residual), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/cyclic-triple-residual).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cyclic-triple-residual/instance.rec

import Definitions.Def_HodgeComputerCyclicTripleResidual

theorem HodgeComputer.CyclicTripleResidual.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.CyclicTripleResidual.n)
      HodgeComputer.CyclicTripleResidual.F
      HodgeComputer.CyclicTripleResidual.A
      HodgeComputer.CyclicTripleResidual.d
      HodgeComputer.CyclicTripleResidual.q := by
  sorry
