-- Prove2me | Theorems.Thm_HighDimCLT_Hyperrect_lemma_A_1
-- name    : HighDimCLT.Hyperrect.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:45.718162+00:00
-- url     : https://prove2.me/theorems/6766ed73-94c7-41b6-8d70-ba924280ac0f
-- title:
--   Lemma A.1 (Nazarov's inequality), p. 2323 — P(Y ≤ y + a) − P(Y ≤ y) ≤ Ca√(log p), C depending only on b
-- statement:
--   This is Nazarov's anti-concentration inequality for Gaussian vectors over lower orthants.
--
--   For every $b > 0$ there is a constant $C > 0$, depending only on $b$, with the following property. Let $p \ge 3$ and let $Y = (Y_1, \dots, Y_p)'$ be a centred Gaussian random vector in $\mathbb R^p$ with $\mathrm E[Y_j^2] \ge b$ for all $j = 1, \dots, p$. Then for every $y \in \mathbb R^p$ and every $a > 0$,
--
--   $$\mathrm P(Y \le y + a) - \mathrm P(Y \le y) \le C a \sqrt{\log p},$$
--
--   where $Y \le y$ means $Y_j \le y_j$ for every $j$ and $y + a = (y_1 + a, \dots, y_p + a)'$.
--
--   The bound controls how much probability a Gaussian vector can put in a thin shell around the boundary of an orthant; its $\sqrt{\log p}$ dependence on the dimension is what makes the high-dimensional CLT possible.
--
--   **Formalization Note** The constant $C$ is quantified after $b$ and before the probability space, $p$, the law of $Y$, $y$ and $a$. "Centred Gaussian" is Mathlib's `HasGaussianLaw` (the law of $Y$ is a Gaussian measure on $\mathbb R^p$, possibly degenerate) together with $\mathrm E[Y_j] = 0$ for every $j$. The paper's standing assumption $p \ge 3$ is stated; at $p = 1$ the right-hand side would be $0$.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2323, App. A, Lemma A.1; standing assumption p ≥ 3 from §1.1, p. 2312

import Mathlib
import Definitions.Def_HighDimCLT_Hyperrect_Setting

open MeasureTheory ProbabilityTheory

namespace HighDimCLT.Hyperrect

universe u

theorem lemma_A_1 :
    ∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (p : ℕ), 3 ≤ p →
      ∀ (Y : Ω → E p), HasGaussianLaw Y P →
        (∀ j, ∫ ω, Y ω j ∂P = 0) →
        (∀ j, b ≤ ∫ ω, Y ω j ^ 2 ∂P) →
      ∀ (y : E p) (a : ℝ), 0 < a →
        P.real {ω | ∀ j, Y ω j ≤ y j + a} - P.real {ω | ∀ j, Y ω j ≤ y j}
          ≤ C * a * Real.sqrt (Real.log p) := by sorry

end HighDimCLT.Hyperrect
