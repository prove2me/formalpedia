-- Prove2me | Theorems.Thm_McLeishCLT_MDA_eq_2_2
-- name    : McLeishCLT.MDA.eq_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:30:12.230993+00:00
-- url     : https://prove2.me/theorems/08aec82f-e763-49b0-954f-fcf59e420499
-- title:
--   (2.2), p. 621 — T_n(U_n − exp(−t²/2)) → 0 in L₁ under (2.1 b, c, d)
-- statement:
--   Let $\{X_{n,j};\ 1\le j\le k_n\}$ be an array of real random variables on a probability space $(\Omega,\mathcal F,P)$ and fix a real $t$. Let $T_n=\prod_{j}(1+itX_{n,j})$ and $U_n=\exp\{-\tfrac{t^2}{2}\sum_jX_{n,j}^2+\sum_j r(X_{n,j}t)\}$, with $r(x)=ix+x^2/2-\log(1+ix)$. Suppose
--
--   1. $\{T_n\}$ is uniformly integrable,
--   2. $\sum_jX_{n,j}^2\to_p1$, and
--   3. $\max_{j\le k_n}|X_{n,j}|\to_p0$.
--
--   Then
--   $$T_n\big(U_n-e^{-t^2/2}\big)\xrightarrow{L_1}0 .$$
--
--   This is the step (2.2) of the proof of Theorem (2.1): since $e^{itS_n}=T_ne^{-t^2/2}+T_n(U_n-e^{-t^2/2})$, it reduces the convergence of the characteristic function of $S_n$ to $E T_n\to1$.
--
--   **Formalization Note** Hypothesis (a) of Theorem (2.1), $ET_n\to1$, is not used for (2.2) and is dropped; uniform integrability is required at the fixed $t$ only, as the uniform integrability of the complex-valued $T_n$ in Mathlib's sense (measurability, a uniform $L_1$ bound and uniformly small tails). The $L_1$ norm is taken in $[0,\infty]$.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 621, display (2.2) in the proof of Theorem (2.1)

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- (2.2), p. 621: under (2.1 b, c, d) at a fixed `t`, `T_n (U_n - exp(-t²/2)) → 0` in `L₁`. -/
theorem eq_2_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hXm : ∀ n, ∀ j < k n, Measurable (X n j)) (t : ℝ)
    (hb : UniformIntegrable (fun n => prodT k X t n) 1 P)
    (hc : TendstoInMeasure P (fun n => sumSq k X n) atTop (fun _ => 1))
    (hd : TendstoInMeasure P (fun n => maxAbs k X n) atTop (fun _ => 0)) :
    Tendsto (fun n => eLpNorm (fun ω => prodT k X t n ω *
      (prodU k X t n ω - Complex.exp (-(t : ℂ) ^ 2 / 2))) 1 P) atTop (𝓝 0) := by sorry

end McLeishCLT.MDA
