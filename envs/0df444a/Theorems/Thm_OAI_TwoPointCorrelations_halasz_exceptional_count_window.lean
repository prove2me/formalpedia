-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_exceptional_count_window
-- name    : OAI.TwoPointCorrelations.halasz_exceptional_count_window
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:09.699261+00:00
-- url     : https://prove2.me/theorems/952312d7-a137-4412-8ab2-4f0ff743f774
-- title:
--   Cofactor polynomials of a masked multiplicative function, when the twisted distance is large except near τ
-- statement:
--   There are $C>0$, $K\ge0$ and $X_0$ such that for all naturals $N$ and reals $a\ge1$ with $\lfloor N/a\rfloor\ge X_0$, every multiplicative $F$ with $F(1)=1$ and $|F(n)|\le1$ ($n\ge1$), all finite sets of primes $Q,P$, and reals $t,\tau$, $M\ge0$: writing $Y=\lfloor 2N/a\rfloor$, if $2M+K\le\mathbb D(F,n^{iv};Y)^2$ (`squaredDistance F (mrtArchimedeanTwist v) Y`, the twist $n\mapsto n^{iv}$) for every $v$ with $|v-t|\le(\log Y)^8$ and $|v-\tau|\ge\tfrac12$, then
--
--   $$\big|\texttt{mrtCofactorPolynomial}\ P\ (F\cdot\mathbf 1_{Q})\ N\ a\ t\big|\le C\Big((\mu+1)e^{-\mu}+\frac{\log\log Y}{\log Y}\Big),\qquad\mu=\min(M,\log(1+|\tau-t|)),$$
--
--   where $F\cdot\mathbf 1_Q$ is `mrtMissingCoefficient F Q`, i.e. $F(n)$ when no prime of $Q$ divides $n$ and $0$ otherwise, and `mrtCofactorPolynomial P G N a t` $=\sum_{1\le m\le4N,\ N<am\le2N}\frac{\texttt{mrtDirichletAtom}\ G\ m\ t}{\#\{p\in P:p\mid m\}+1}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_exceptional_count_window`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical
open scoped ComplexConjugate

theorem halasz_exceptional_count_window :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (Q P : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ (t τ M : ℝ), 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 →
        1/2 ≤ |v-τ| → 2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤ C *
        ((min M (Real.log (1+|τ-t|)) + 1) * Real.exp (-min M (Real.log (1+|τ-t|))) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
