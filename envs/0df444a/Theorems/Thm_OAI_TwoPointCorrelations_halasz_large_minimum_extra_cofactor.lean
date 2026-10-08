-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_large_minimum_extra_cofactor
-- name    : OAI.TwoPointCorrelations.halasz_large_minimum_extra_cofactor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:08.919335+00:00
-- url     : https://prove2.me/theorems/55879a41-69d2-453a-862d-9cd02c5ef4c3
-- title:
--   Cofactor polynomials of typical numbers are small when every twisted distance is large
-- statement:
--   For all sufficiently large $N$: let $F$ be multiplicative with $F(1)=1$, $|F(n)|\le1$ ($n\ge1$), and suppose $\mathbb D(F,n^{iv};2N)^2\ge\frac1{10}\log\log(2N)$ for every $|v|\le2N$ (`squaredDistance F (mrtArchimedeanTwist v) (2N)`). Let $P,Q$ be reals and $J$ natural with $\log Q\ge1$ and $\exp(J^{4J+2}(\log Q)^J)\le\exp(\sqrt{\log N})$, $A$ a finite set of primes, $a\in[1,\exp(\log N/\log\log N)]$ and $|t|\le N$. Then
--
--   $$\big|\texttt{mrtCofactorPolynomial}\ A\ G\ N\ a\ t\big|\le2(\log N)^{-1/40},$$
--
--   with $G$ = `mrtTypicalCoefficient (Icc 1 J) (j ↦ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F`: $F(n)$ if each of the $J$ prime bands $(\exp(j^{4j}(\log Q)^{j-1}\log P),\exp(j^{4j+2}(\log Q)^j)]$ contains a prime divisor of $n$, else $0$; and `mrtCofactorPolynomial A G N a t` $=\sum_{1\le m\le4N,\ N<am\le2N}G(m)m^{-1-it}/(\#\{p\in A:p\mid m\}+1)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_large_minimum_extra_cofactor`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem halasz_large_minimum_extra_cofactor :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      (∀ v : ℝ, |v| ≤ 2*N → (1/10:ℝ)*Real.log (Real.log (2*N:ℕ)) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
