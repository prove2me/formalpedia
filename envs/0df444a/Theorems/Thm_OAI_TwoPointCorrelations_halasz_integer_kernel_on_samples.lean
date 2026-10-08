-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_integer_kernel_on_samples
-- name    : OAI.TwoPointCorrelations.halasz_integer_kernel_on_samples
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:52.068675+00:00
-- url     : https://prove2.me/theorems/a569af3d-928e-4cec-9d11-0a85d48b1e1e
-- title:
--   The triangle-weighted exponential polynomial kernel decays like 1/(1+(t−s)²) on samples
-- statement:
--   Let $M>0$, $T\ge0$, and $S$ a finite set of reals with $|t|\le T$ for $t\in S$. Then for all $t,s\in S$,
--
--   $$\Big|\sum_{0\le n\le\lceil5M/2\rceil}w_M(n)\,n^{-i(t-s)}\Big|\le\frac{18600M}{1+(t-s)^2}+E(M,T),$$
--
--   where $w_M(x)=\max(0,\min(2x/M-1,\,5-2x/M))$ (`halaszTriangleWeight M`), the term $n^{-i(t-s)}$ means $\exp(-i(t-s)\log n)$ (with $\log0=0$), and $E(M,T)$ = `halaszSparseKernelError M T` $=\frac{440}{\pi}\sqrt{2T}+\frac{512}{M(2\pi)^2}\sum_{k\in\mathbb Z}k^{-2}$ (the sum with Lean's convention $1/0=0$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_integer_kernel_on_samples`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_integer_kernel_on_samples (M T : ℝ) (hM : 0 < M) (_hT : 0 ≤ T)
    (S : Finset ℝ) (hS : ∀ t ∈ S, |t| ≤ T) :
    ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial (halaszTriangleSupport M)
        (fun n => (halaszTriangleWeight M n:ℂ)) (fun n => -Real.log n) (t-s)‖ ≤
      (18600*M)/(1+(t-s)^2)+halaszSparseKernelError M T := by
  sorry

end OAI.TwoPointCorrelations
