-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_remark_2
-- name    : MultivarScores.LevelSet.remark_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:49.644547+00:00
-- url     : https://prove2.me/theorems/17f1e271-3e0a-4696-a17d-3771252a3364
-- title:
--   Remark 2, p. 17 — for d = 1, (13) with A = [q, ∞) plus (1 − α)∫𝟙{z ≥ y}h equals the quantile score (α − 𝟙{y < q})(H(y) − H(q))
-- statement:
--   Let $h:\mathbb R\to\mathbb R$ be measurable, nonnegative and integrable, and let $\alpha,q,y\in\mathbb R$. Identify a quantile estimate $q=q(\alpha)$ with the Borel set $A=[q,\infty)$. Then
--
--   $$\int_{-\infty}^{\infty}\bigl(\alpha-\mathbb 1\{z\ge y\}\bigr)\mathbb 1\{z\ge q\}h(z)\,dz+(1-\alpha)\int_{-\infty}^{\infty}\mathbb 1\{z\ge y\}h(z)\,dz=\bigl(\alpha-\mathbb 1\{y<q\}\bigr)\int_q^y h(z)\,dz ,$$
--
--   where $\int_q^y=-\int_y^q$ when $y<q$. With $H$ an antiderivative of $h$, the right-hand side is $(\alpha-\mathbb 1\{y<q\})(H(y)-H(q))$, the general quantile score. Since the added term depends only on $y$, the CDF level set score (13) in dimension one is equivalent to the full class of quantile scores.
--
--   **Formalization Note** The statement is on $\mathbb R$ directly. $H(y)-H(q)$ is written as the oriented integral $\int_q^y h$ (`intervalIntegral`), which is the same for every antiderivative.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 17, Remark 2

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem remark_2 (h : ℝ → ℝ) (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z)
    (hh_int : Integrable h) (α q y : ℝ) :
    (∫ z in Set.Ici q, (α - if y ≤ z then 1 else 0) * h z) + (1 - α) * ∫ z in Set.Ici y, h z =
      (α - if y < q then 1 else 0) * ∫ z in q..y, h z := by sorry

end MultivarScores.LevelSet
