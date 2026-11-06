-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_certificate
-- name    : HodgeComputer.DiagonalPermutation.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:03:39.017301+00:00
-- url     : https://prove2.me/theorems/be901a67-adc3-4525-b8cd-0c5eff1d3727
-- title:
--   Simultaneous permutations · standard sector — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Simultaneous permutations · standard sector”](https://hodge.computer/#case/diagonal-permutation), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/diagonal-permutation).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/diagonal-permutation/instance.rec

import Definitions.Def_HodgeComputerDiagonalPermutation

theorem HodgeComputer.DiagonalPermutation.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.DiagonalPermutation.n)
      HodgeComputer.DiagonalPermutation.F
      HodgeComputer.DiagonalPermutation.A
      HodgeComputer.DiagonalPermutation.d
      HodgeComputer.DiagonalPermutation.q := by
  sorry
