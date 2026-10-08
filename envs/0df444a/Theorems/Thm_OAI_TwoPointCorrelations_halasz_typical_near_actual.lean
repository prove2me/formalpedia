-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_near_actual
-- name    : OAI.TwoPointCorrelations.halasz_typical_near_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:01.018982+00:00
-- url     : https://prove2.me/theorems/36952182-d09c-422c-be5d-b9ccd2de0993
-- title:
--   Mean square of the typical dyadic polynomial near the minimizing frequency
-- statement:
--   There is $C>0$ such that for all sufficiently large $N$: for reals $2\le P\le Q$ with $\log P>1$ and $J\ge1$ with $\exp(j^{4j+2}(\log Q)^j)\le\exp(\sqrt{\log N})$ for $j=1..J$; every completely multiplicative $F$ on positive integers with $F(1)=1$, $|F|\le1$; every $X\le N^3$ and reals $\tau,T,M$ with $M\ge0$, $|\tau|+(\log2N)^8\le T$, $\mathbb D(F,n^{iv};X)^2\ge M$ for $|v|\le T$, and $\mathbb D(F,n^{i\tau};2N)^2\le\frac1{10}\log\log(2N)$:
--
--   $$\int_{-(\log N)^{1/16}}^{(\log N)^{1/16}}\big|D_N(\tau+u)\big|^2du\le C\big(e^{-4M/5}+(\log N)^{-1/32}\big),$$
--
--   where $D_N(t)=\sum_{N<n\le2N}\frac{G(n)}nn^{-it}$ for $G$ the restriction of $F$ to the integers with a prime factor in each band $(\mathrm{lo}_j,\mathrm{up}_j]$, $j=1..J$ (`mrtTypicalCoefficient`, `mrtPrimeBand`, `mrtBandLower`, `mrtBandUpper`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_typical_near_actual`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open MeasureTheory
open scoped Classical

theorem halasz_typical_near_actual : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ (P Q : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ J →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, F 1=1 →
      (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ (X : ℕ) (τ T M : ℝ), X ≤ N^3 → 0 ≤ M → |τ|+Real.log (2*N:ℕ)^8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤ Real.log (Real.log (2*N:ℕ))/10 →
      (∫ u in -((Real.log N)^(1/16:ℝ))..((Real.log N)^(1/16:ℝ)),
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N (τ+u)‖^2) ≤
        C*(Real.exp (-4*M/5)+(Real.log N)^(-1/32:ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
