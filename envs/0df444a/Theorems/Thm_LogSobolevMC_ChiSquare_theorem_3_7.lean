-- Prove2me | Theorems.Thm_LogSobolevMC_ChiSquare_theorem_3_7
-- name    : LogSobolevMC.ChiSquare.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:32.427782+00:00
-- url     : https://prove2.me/theorems/aba7fa93-5119-42a6-8b97-b5367a36d0d1
-- title:
--   Theorem 3.7 — chi-square convergence from log-Sobolev inequalities
-- statement:
--   Let $K$ be an irreducible finite-state Markov chain with positive stationary distribution $\pi$. Write $\alpha$ for its log-Sobolev constant, $\lambda$ for its variational spectral gap, and $h_t^x(y)=H_t(x,y)/\pi(y)$. Fix a state $x$ with $\pi(x)\le e^{-1}$ and a real number $c>0$. Then
--
--   $$
--   \|h_t^x-1\|_2\le e^{1-c}\quad\text{at }t=\frac{1}{2\alpha}\log\log\frac1{\pi(x)}+\frac c\lambda.
--   $$
--
--   If $(K,\pi)$ is reversible, the same bound holds at the earlier time
--
--   $$
--   t=\frac{1}{4\alpha}\log\log\frac1{\pi(x)}+\frac c\lambda.
--   $$
--
--   The theorem bounds the chi-square distance of a heat-kernel row from stationarity in terms of the log-Sobolev constant and spectral gap. The two conclusions retain the distinct general and reversible constants.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 723, Theorem 3.7, https://doi.org/10.1214/aoap/1034968224

import Mathlib
import Definitions.Def_LogSobolevMC_ChiSquare_Setting

namespace LogSobolevMC.ChiSquare

theorem theorem_3_7 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hirr : MarkovMixing.Irreducible K)
    (x : V) (hx : π x ≤ Real.exp (-1)) (c : ℝ) (hc : 0 < c) :
    let L := Real.log (Real.log (1 / π x))
    (lpNorm π 2 (fun y =>
      density K π ((2 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
        Real.exp (1 - c)) ∧
    (MarkovMixing.DetailedBalance K π →
      lpNorm π 2 (fun y =>
        density K π ((4 * logSobolev K π)⁻¹ * L + c / gap K π) x y - 1) ≤
          Real.exp (1 - c)) := by sorry

end LogSobolevMC.ChiSquare
