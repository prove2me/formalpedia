-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_phase_from_polynomial
-- name    : OAI.TwoPointCorrelations.halasz_phase_from_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:52.29274+00:00
-- url     : https://prove2.me/theorems/16a5d427-82c7-452c-be82-663f3f324333
-- title:
--   From bounds for Vinogradov polynomials to bounds for the exponential sum of t·log(N+a+n)
-- statement:
--   Let $N\ge1$, $H\le N$, $k$ naturals, and reals $a\in[0,1]$, $t$, $\alpha\in[0,1/3]$, $\lambda$, $A\ge0$ with $N^{2/3}\le N/2$, $|t|=N^\lambda$ and $\lambda+(2\alpha-1)(k+1)\le-\frac12$. Let $M=\lfloor N^\alpha\rfloor$ (`halaszShortScale N α`) and suppose that for every $z\in[N,2N]$,
--
--   $$\frac1{M^2}\Big|\sum_{b=1}^MV_{k,M}\big((\gamma_j(z)b^j)_{j=1}^k\big)\Big|\le A,\qquad\gamma_j(z)=\frac{t(-1)^{j-1}}{2\pi jz^j}.$$
--
--   Then
--
--   $$\Big|\sum_{n=0}^{H-1}\exp\big(it\log(N+a+n)\big)\Big|\le NA+4N^{2/3}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_phase_from_polynomial`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Complex

theorem halasz_phase_from_polynomial {N H k : ℕ} (hN : 1≤ N) (hH : H≤ N)
    {a t α lam A : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hα : 0≤α) (hαhi : α≤1/3)
    (hA : 0≤ A) (hhalf : (N:ℝ)^(2/3:ℝ)≤(N:ℝ)/2) (ht : |t|=(N:ℝ)^lam)
    (htaylor : lam+(2*α-1)*((k:ℝ)+1)≤-(1/2:ℝ))
    (hpoly : ∀ z∈Set.Icc (N:ℝ) (2*N),
      ‖∑ b : Fin (halaszShortScale N α),halaszVinogradovPolynomial k (halaszShortScale N α)
        (halaszScaledFrequency (halaszLogCoefficient t z)
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(halaszShortScale N α:ℝ)^2≤ A) :
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log ((N:ℝ)+a+n):ℝ):ℂ))‖≤
      (N:ℝ)*A+4*(N:ℝ)^(2/3:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
