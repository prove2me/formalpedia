-- Prove2me | Theorems.Thm_McLeishCLT_MDA_trunc_lintegral_normSq_prodT_le
-- name    : McLeishCLT.MDA.trunc_lintegral_normSq_prodT_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:43.086288+00:00
-- url     : https://prove2.me/theorems/15d99d57-37b2-472d-9a9b-be2fdd10da8d
-- title:
--   p. 622, proof of (2.3) — E|T_n|² ≤ e^{2t²}(1 + t²EX²_{n,J_n}) for the truncated array
-- statement:
--   Let $\{X_{n,j};\ 1\le j\le k_n\}$ be an array of real random variables on a probability space, $Z_{n,j}=X_{n,j}\,I(\sum_{k=1}^{j-1}X_{n,k}^2\le2)$, $T_n=\prod_{j=1}^{k_n}(1+itZ_{n,j})$ for real $t$, and
--   $$J_n=\min\Big\{j\le k_n:\ \sum_{i=1}^{j}X_{n,i}^2>2\Big\}\ \text{ if }\sum_iX_{n,i}^2>2,\qquad J_n=k_n\ \text{ otherwise.}$$
--   Then for every real $t$ and every $n$
--   $$E|T_n|^2\le e^{2t^2}\big(1+t^2EX_{n,J_n}^2\big).$$
--
--   This is the bound by which McLeish verifies uniform integrability (2.1 b) for the truncated array.
--
--   **Formalization Note** Both expectations are lower Lebesgue integrals in $[0,\infty]$, so the inequality is meaningful even when $EX_{n,J_n}^2=\infty$. $J_n$ is 0-based in Lean; for an empty row ($k_n=0$) the left side is $1$ and the inequality holds trivially.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 622, proof of Theorem (2.3), display bounding E|T_n|²

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- p. 622, proof of (2.3): `E|T_n|² ≤ e^{2t²} (1 + t² E X²_{n,J_n})` for the truncated array. -/
theorem trunc_lintegral_normSq_prodT_le {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (t : ℝ) (n : ℕ) :
    ∫⁻ ω, ‖prodT k (trunc X) t n ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (Real.exp (2 * t ^ 2)) *
        (1 + ENNReal.ofReal (t ^ 2) * ∫⁻ ω, ‖X n (stopJ k X n ω) ω‖ₑ ^ 2 ∂P) := by sorry

end McLeishCLT.MDA
