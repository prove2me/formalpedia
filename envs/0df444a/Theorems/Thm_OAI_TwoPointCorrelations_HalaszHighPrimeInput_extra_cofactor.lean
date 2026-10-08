-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_HalaszHighPrimeInput_extra_cofactor
-- name    : OAI.TwoPointCorrelations.HalaszHighPrimeInput.extra_cofactor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:29.704972+00:00
-- url     : https://prove2.me/theorems/06d7fe6f-07c4-4d26-95bb-473133ff8591
-- title:
--   Under the high-prime cosine input, cofactor polynomials of typical numbers are small far from the minimizing twist
-- statement:
--   Assume `HalaszHighPrimeInput` (for all large $X$ and $(\log X)^{20}\le|u|\le2X$: $\sum_{p\le X}(1-|\cos(\frac u2\log p)|)/p\ge\frac1{10}\log\log X$). Then for all sufficiently large $N$: for every multiplicative $F$ with $F(1)=1$ and $|F(n)|\le1$ ($n\ge1$), reals $P,Q$ and natural $J$ with $\log Q\ge1$ and $\mathrm{up}_J:=\exp(J^{4J+2}(\log Q)^J)\le\exp(\sqrt{\log N})$ (`mrtBandUpper Q J`), every finite set $A$ of primes, every $a\in[1,\exp(\log N/\log\log N)]$, and reals $t,\tau$ with $|t|\le N$, $|\tau|\le2N$, if $\tau$ minimizes $v\mapsto\mathbb D(F,n^{iv};2N)^2$ over $|v|\le2N$ and $|t-\tau|\ge(\log N)^{1/16}$, then
--
--   $$\big|\texttt{mrtCofactorPolynomial}\ A\ G\ N\ a\ t\big|\le2(\log N)^{-1/40},$$
--
--   where $G$ = `mrtTypicalCoefficient (Icc 1 J) (j ↦ primes in (lo_j, up_j]) F` is $F(n)$ if for every $j\in\{1..J\}$ some prime of the $j$-th band (`mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)`, the primes in $(\mathrm{lo}_j,\mathrm{up}_j]$ with $\mathrm{lo}_j=\exp(j^{4j}(\log Q)^{j-1}\log P)$) divides $n$, and $0$ otherwise; and `mrtCofactorPolynomial A G N a t` $=\sum_{1\le m\le4N,\ N<am\le2N}\frac{G(m)m^{-1-it}}{\#\{p\in A:p\mid m\}+1}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.HalaszHighPrimeInput.extra_cofactor`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem HalaszHighPrimeInput.extra_cofactor (hhigh : HalaszHighPrimeInput) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t τ : ℝ, |t| ≤ N → |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      (Real.log N)^(1/16:ℝ) ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
