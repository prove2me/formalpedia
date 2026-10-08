-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_AC0Circuit_fourier_tail_polynomial_degree
-- name    : OAI.TwoPointCorrelations.AC0Circuit.fourier_tail_polynomial_degree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:08.513116+00:00
-- url     : https://prove2.me/theorems/c30655bc-7778-4fb4-8875-f6526ce85913
-- title:
--   Linial–Mansour–Nisan-type Fourier tail bound for AC⁰ circuits
-- statement:
--   Let $c$ be an AC⁰ circuit on $n$ inputs (`AC0Circuit n`: literals and unbounded fan-in AND/OR gates) of depth at most $d$, and let $r\ge1$. Let $\mathbf 1_c:\{0,1\}^n\to\{0,1\}$ be its indicator, and let $T_D\mathbf 1_c$ be its Walsh–Fourier truncation to degree $D$, $\sum_{|S|\le D}\widehat{\mathbf 1_c}(S)\,\chi_S$ (`walshTruncation`), at the degree $D=8(r+1)\,(24(2r+3)^2)^d$ (`switchingDegree d r`). Then, averaging uniformly over the cube,
--
--   $$\mathbb E_x\Big[\big(\mathbf 1_c(x)-T_D\mathbf 1_c(x)\big)^2\Big]\le 4\,\mathrm{size}(c)\,(1/2)^{r+1},$$
--
--   where the size counts every literal and every gate.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.AC0Circuit.fourier_tail_polynomial_degree`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open scoped Classical

theorem AC0Circuit.fourier_tail_polynomial_degree {n : ℕ} (c : AC0Circuit n)
    (d r : ℕ) (hc : c.depth ≤ d) (hr : 1 ≤ r) :
    cubeAverage (fun x => (c.indicator x -
      walshTruncation c.indicator (switchingDegree d r) x) ^ 2) ≤
      4 * (c.size : ℝ) * (1 / 2 : ℝ) ^ (r + 1) := by
  sorry

end OAI.TwoPointCorrelations
