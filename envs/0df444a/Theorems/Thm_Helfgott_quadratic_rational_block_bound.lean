-- Prove2me | Theorems.Thm_Helfgott_quadratic_rational_block_bound
-- name    : Helfgott.quadratic_rational_block_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T17:36:01.802647+00:00
-- url     : https://prove2.me/theorems/7ad0938f-b672-447a-8d47-68209997f0b9
-- title:
--   A log-free capped reciprocal-square sine bound on a rational block
-- statement:
--   Let $q\ge2$, $(|a|,q)=1$, $\alpha=a/q+\beta$, and $|\beta|\le q^{-2}$. For $0\le N\le q$, arbitrary real offset $M$ and phase $\theta$, and $A,C\ge0$, define $F(t)=\min(A,C/\sin^2t)$ away from sine zeros and $F(t)=A$ at a sine zero. Then
--
--   $$\sum_{j=0}^{N-1}F(\pi\alpha(M+j)+\theta)
--   \le 2A+\min\{2Cq^2,\ A+2q\sqrt{AC}\}.$$
--
--   This conservative Type I kernel estimate has no logarithmic loss. It includes arbitrary shifts, signed numerators, short blocks, zero coefficients, and exact resonances. It does not assert Helfgott's sharper published constants or a complete Vaughan estimate.
-- source:
--   Classical rational-grid spacing and reciprocal-square summation, in the role of Lemma 3.1 of H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252v4. Constants here are conservative. The spacing proof is adapted with attribution from accepted Prove2Me submission 968ef56d-d4b0-42b8-99aa-5a18c7253fab by marwahaha, retaining the Apache 2.0 attribution to Gershon Bialer. The capped quadratic-series and kernel proofs are new Lean proofs written by Codex.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
open scoped BigOperators

theorem Helfgott.quadratic_rational_block_bound (a : ℤ) (q N : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (hN : N ≤ q) (alpha beta theta M A C : ℝ)
    (halpha : alpha = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ Finset.range N,
      if Real.sin (Real.pi*alpha*(M+(j:ℝ))+theta) = 0 then A
      else min A (C/(Real.sin (Real.pi*alpha*(M+(j:ℝ))+theta))^2)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by sorry
