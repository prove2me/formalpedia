-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_near_renormalization
-- name    : OAI.TwoPointCorrelations.halasz_near_renormalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:53.137986+00:00
-- url     : https://prove2.me/theorems/5ee1cb91-ffa9-4e95-8029-77fd7d85013e
-- title:
--   Renormalizing the phase mean of a twisted masked multiplicative function near its minimizing frequency
-- statement:
--   For all sufficiently large $N$: let $F$ be multiplicative with $F(1)=1$ and $|F(n)|\le1$ ($n\ge1$), $Q$ a finite set of primes each at most $\exp(\sqrt{\log N})$, and $t$ real with $\mathbb D(F,n^{it};N)^2\le\frac18\log\log N$. Let $G(n)=F_Q(n)\,n^{-it}$ (`halaszTwistedFunction (mrtMissingCoefficient F Q) t`, with $F_Q$ equal to $F$ off the multiples of primes of $Q$ and $0$ on them). Then for every real $u$ with $|u|\le(\log N)^{1/16}$,
--
--   $$\Big|\Phi_G(u,N)-\frac{N^{-iu}}{1-iu}\,\Phi_G(0,N)\Big|\le36\,(c_1+1)\,e^8\,N(\log N)^{-1/16},$$
--
--   where $\Phi_G(u,N)=\sum_{n=1}^NG(n)\,n^{-iu}$ (`halaszPhaseMean`, with $n^{-iu}=\exp(-iu\log n)$ = `halaszPowerPhase u n`) and $c_1$ = `halaszPrimePowerLogConstant` $=2\log4+32/\log2$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_near_renormalization`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter

theorem halasz_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      ∀ u : ℝ, |u| ≤ (Real.log N) ^ (1 / (16 : ℝ)) →
      let G := halaszTwistedFunction (mrtMissingCoefficient F Q) t
      ‖halaszPhaseMean G u N -
        (halaszPowerPhase u N / (1 + (-u : ℂ) * Complex.I)) * halaszPhaseMean G 0 N‖ ≤
      (36 * (halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        (Real.log N) ^ (-1 / (16 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
