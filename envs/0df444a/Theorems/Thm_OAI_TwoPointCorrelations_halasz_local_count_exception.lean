-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_local_count_exception
-- name    : OAI.TwoPointCorrelations.halasz_local_count_exception
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:02.094461+00:00
-- url     : https://prove2.me/theorems/5098349f-96ec-434e-bda1-afad34f61be4
-- title:
--   Halász bound for a prime-masked multiplicative sum weighted by 1/(ω_P(n)+1), away from one frequency
-- statement:
--   There are $C>0$ and $X_0$ such that for every natural $N\ge X_0$, every multiplicative $F$ with $F(1)=1$ and $|F(n)|\le1$ ($n\ge1$), all finite sets of primes $Q,P$, and reals $t,\tau$, $M\ge0$: if $2M\le\mathbb D(F,n^{iv};N)^2$ for every $v$ with $|v-t|\le(\log N)^8$ and $|v-\tau|\ge\frac12$, then
--
--   $$\Big|\sum_{n=1}^N\frac{F_Q(n)\,n^{-it}}{\omega_P(n)+1}\Big|\le CN\Big((\mu+1)e^{-\mu}+\frac{\log\log N}{\log N}\Big),\qquad\mu=\min(M,\log(1+|\tau-t|)),$$
--
--   where $F_Q(n)$ = `mrtMissingCoefficient F Q n` is $F(n)$ if no prime of $Q$ divides $n$ and $0$ otherwise, $n^{-it}=\overline{\exp(it\log n)}$, and $\omega_P(n)$ is the number of primes of $P$ dividing $n$ (`finitePrimeDivisorCount`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_local_count_exception`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical
open scoped ComplexConjugate

theorem halasz_local_count_exception : ∃ C X₀ : ℝ, 0 < C ∧
    ∀ N : ℕ, X₀ ≤ N →
    ∀ F : ℕ → ℂ, F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ Q P : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ t τ M : ℝ, 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (N:ℝ)^8 →
        1/2 ≤ |v-τ| → 2*M ≤ squaredDistance F (mrtArchimedeanTwist v) N) →
      ‖∑ n ∈ Icc 1 N, (mrtMissingCoefficient F Q n * conj (mrtArchimedeanTwist t n)) /
        ((finitePrimeDivisorCount P n : ℂ)+1)‖ ≤
      C*N*((min M (Real.log (1+|τ-t|))+1)*Real.exp (-min M (Real.log (1+|τ-t|)))+
          Real.log (Real.log N)/Real.log N) := by
  sorry

end OAI.TwoPointCorrelations
