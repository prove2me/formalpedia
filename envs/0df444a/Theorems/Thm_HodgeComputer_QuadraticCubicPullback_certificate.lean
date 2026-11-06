-- Prove2me | Theorems.Thm_HodgeComputer_QuadraticCubicPullback_certificate
-- name    : HodgeComputer.QuadraticCubicPullback.certificate
-- status  : Open
-- author  : @benediamond
-- created : 2026-11-05T22:10:21.723696+00:00
-- url     : https://prove2.me/theorems/1bf1de52-286c-4e37-87a7-0b5a718fd6e6
-- title:
--   Quadratic pullback · residual density — certificate
-- statement:
--   For $q=1$, and the fixed $(F,A)$ of [“Quadratic pullback · residual density”](https://hodge.computer/#case/quadratic-cubic-pullback), prove the existence of a rational vector field $v$ with components homogeneous of degree $1$ and common denominator relatively prime to $F$, satisfying $F^{2}\mid A-1\cdot dF(v)+F\cdot\operatorname{div}(v)$. Divisibility is in the localization with denominators relatively prime to $F$. There is no denominator degree bound. [More details](https://hodge.computer/#case/quadratic-cubic-pullback).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/quadratic-cubic-pullback/instance.rec

import Definitions.Def_HodgeComputerQuadraticCubicPullback

theorem HodgeComputer.QuadraticCubicPullback.certificate :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.QuadraticCubicPullback.n)
      HodgeComputer.QuadraticCubicPullback.F
      HodgeComputer.QuadraticCubicPullback.A
      HodgeComputer.QuadraticCubicPullback.d
      HodgeComputer.QuadraticCubicPullback.q := by
  sorry
