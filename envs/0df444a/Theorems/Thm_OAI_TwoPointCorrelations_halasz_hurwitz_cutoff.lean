-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_hurwitz_cutoff
-- name    : OAI.TwoPointCorrelations.halasz_hurwitz_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:41.689997+00:00
-- url     : https://prove2.me/theorems/c46bf33e-84d0-4757-b7e7-9c8e669299e3
-- title:
--   Truncation of the Hurwitz zeta function at N terms, with explicit error
-- statement:
--   Let $a\in[0,1]$, $s\in\mathbb C$ with $\operatorname{Re}s>0$ and $s\ne1$, and $N\ge1$. Then
--
--   $$\Big|\zeta(s,a)-a^{-s}\mathbf 1_{a\ne0}-\sum_{n=0}^{N-1}(n+1+a)^{-s}\Big|\le\frac{N^{1-\operatorname{Re}s}}{|1-s|}+\frac{N^{-\operatorname{Re}s}}2+\frac{2|s|\,N^{-\operatorname{Re}s}}{\operatorname{Re}s},$$
--
--   where $\zeta(s,a)$ is Mathlib's `hurwitzZeta` at the point $a$ of $\mathbb R/\mathbb Z$, the term $a^{-s}\mathbf 1_{a\ne0}$ is `mrtHurwitzFirstTerm a s` (zero when $a=0$), and complex powers are Mathlib's principal-branch powers.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_hurwitz_cutoff`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open HurwitzZeta
open MeasureTheory
open Finset
open _root_.Erdos970

theorem halasz_hurwitz_cutoff {a : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    {s : ℂ} (hs : 0< s.re) (hs1 : s≠1) {N : ℕ} (hN : 1≤ N) :
    ‖hurwitzZeta (a:UnitAddCircle) s-mrtHurwitzFirstTerm a s-
      (∑ n∈range N,(((n+1:ℕ):ℝ)+a:ℂ)^(-s))‖≤
      (N:ℝ)^(1-s.re)/‖1-s‖+(N:ℝ)^(-s.re)/2+
        2*‖s‖*(N:ℝ)^(-s.re)/s.re := by
  sorry

end OAI.TwoPointCorrelations
