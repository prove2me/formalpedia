-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_lemma_4
-- name    : KhachiyanRound.BCD.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:50.74398+00:00
-- url     : https://prove2.me/theorems/a1f8c010-7396-4d5d-ab6a-8ff731ffd0c7
-- title:
--   Lemma 4, p. 313 — the BCD reaches (2.10) within K(ε) = O(n(ε⁻¹ + ln n + ln ln m)) iterations
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $n \ge 2$, let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ be centrally symmetric (2.1) and full-dimensional (2.2), let $\varepsilon > 0$, and let $p_0, p_1,\dots$ be any run of the BCD method. Then some iterate $p_k$ with
--   $$k \le C\, n\big(\varepsilon^{-1} + \ln n + \ln\ln m\big)$$
--   satisfies the $\varepsilon$-relaxed optimality conditions (2.10): $w_j(p_k) \le (1+\varepsilon)n$ for all $j$.
--
--   This is the iteration bound (2.23) of the method, $K(\varepsilon) = O(n(\varepsilon^{-1} + \ln n + \ln\ln m))$.
--
--   **Formalization Note** The $O(\cdot)$ is a single constant $C$ quantified before the dimension, the points, $\varepsilon$ and the run, so it is independent of all of them. The statement bounds the index of an iterate meeting the stopping test, uniformly over all tie-breaking rules for the coordinate $r$. Under (2.1), (2.2) and $n\ge2$ one has $m \ge 2n \ge 4$, so $\ln\ln m > 0$.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 313, Lemma 4, (2.23)

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem lemma_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 2 ≤ n → IsCentrallySymmetric a →
      affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε → ∀ p : ℕ → Fin m → ℝ, IsBCDRun a p →
        ∃ k : ℕ, (k : ℝ) ≤ C * n * (1 / ε + Real.log n + Real.log (Real.log m)) ∧
          IsRelaxedOpt a (p k) ε := by sorry
end KhachiyanRound.BCD
