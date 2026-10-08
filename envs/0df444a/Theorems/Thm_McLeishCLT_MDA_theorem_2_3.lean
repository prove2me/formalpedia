-- Prove2me | Theorems.Thm_McLeishCLT_MDA_theorem_2_3
-- name    : McLeishCLT.MDA.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:06.541471+00:00
-- url     : https://prove2.me/theorems/79601f6d-2150-4a8a-ad5e-41beb6bf942c
-- title:
--   Theorem (2.3), p. 621 — an m.d.a. with max_i|X_{n,i}| bounded in L₂ and →_p 0, and Σ_i X²_{n,i} →_p 1, has S_n →_w N(0, 1)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and, for each $n$, let $\{X_{n,i};\ 1\le i\le k_n\}$ be a martingale difference array with respect to an increasing family of sub-σ-fields $\mathcal F_{n,0}\subset\cdots\subset\mathcal F_{n,k_n}$ of row $n$: each $X_{n,i}$ is $\mathcal F_{n,i}$-measurable and integrable, and $E(X_{n,i}\mid\mathcal F_{n,i-1})=0$ a.s. Let $S_n=\sum_iX_{n,i}$. Suppose
--
--   1. $\max_{i\le k_n}|X_{n,i}|$ is uniformly bounded in $L_2$ norm,
--   2. $\max_{i\le k_n}|X_{n,i}|\to_p0$, and
--   3. $\sum_iX_{n,i}^2\to_p1$.
--
--   Then
--   $$S_n\xrightarrow{w}N(0,1).$$
--
--   This is the main central limit theorem of the paper. It needs neither finite variances of the individual summands beyond (1) nor the full Lindeberg condition, and it replaces the conditional variances of Brown and Dvoretsky by the sum of squares.
--
--   **Formalization Note** Each row has its own filtration, the row lengths $k_n$ are arbitrary, and integrability of each $X_{n,i}$ is part of the m.d.a. predicate. Condition (1) is $\sup_n\|\max_i|X_{n,i}|\|_2<\infty$, with the norm in $[0,\infty]$ and a finite bound. Convergence in distribution is Mathlib's `TendstoInDistribution` towards the law of the identity under the standard Gaussian measure.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 621, Theorem (2.3)

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem (2.3), p. 621. -/
theorem theorem_2_3 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X)
    (ha : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, eLpNorm (maxAbs k X n) 2 P ≤ C)
    (hb : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0))
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1)) :
    TendstoInDistribution (fun n => S k X n) atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by sorry

end McLeishCLT.MDA
