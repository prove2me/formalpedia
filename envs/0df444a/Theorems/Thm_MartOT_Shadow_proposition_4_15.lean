-- Prove2me | Theorems.Thm_MartOT_Shadow_proposition_4_15
-- name    : MartOT.Shadow.proposition_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:36.682988+00:00
-- url     : https://prove2.me/theorems/12a1d140-e356-4ee8-9373-29c634c383b1
-- title:
--   Proposition 4.15, p. 29 — for µ_n ⪯C-increasing with µ_n ⪯C µ ⪯E ν, µ_n and S^ν(µ_n) converge and lim S^ν(µ_n) = S^ν(lim µ_n)
-- statement:
--   Let $\mu,\nu$ and $\mu_n$ ($n\in\mathbb N$) be finite Borel measures on $\mathbb R$ with finite first moment. Assume that $(\mu_n)_n$ is increasing in the convex order, $\mu_n\preceq_C\mu_{n+1}$, and that
--   $$\mu_n\preceq_C\mu\preceq_E\nu\qquad\text{for every }n\in\mathbb N .$$
--   Then both $(\mu_n)_n$ and $(S^\nu(\mu_n))_n$ converge weakly in $\mathcal M$, and if $\mu_\infty$ and $S_\infty$ denote the limits, $S_\infty$ is the shadow of $\mu_\infty$ in $\nu$:
--   $$S_\infty=S^\nu(\mu_\infty).$$
--
--   This continuity of the shadow along convex-order increasing sequences is what passes the associativity of shadows from atomic measures to general ones.
--
--   **Formalization Note** $(S^\nu(\mu_n))_n$ is any sequence $(S_n)$ with $S_n$ a shadow of $\mu_n$ in $\nu$ (these exist and are unique by Lemma 4.6, since $\mu_n\preceq_C\mu\preceq_E\nu$). The conclusion asserts limits $\mu_\infty,S_\infty\in\mathcal M$ of the two sequences with $S_\infty$ a shadow of $\mu_\infty$ in $\nu$; limits in $\mathcal M$ are unique. Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Proposition 4.15, p. 29

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_ConvergesInM

namespace MartOT.Shadow

open MeasureTheory

theorem proposition_4_15 (μs : ℕ → Measure ℝ) (μ ν : Measure ℝ)
    (hmono : ∀ n, MartOT.Var.ConvexLE (μs n) (μs (n + 1))) (hle : ∀ n, MartOT.Var.ConvexLE (μs n) μ)
    (hE : MartOT.Var.ExtConvexLE μ ν) (Ss : ℕ → Measure ℝ) (hS : ∀ n, MartOT.Var.IsShadow ν (μs n) (Ss n)) :
    ∃ μInf SInf : Measure ℝ, ConvergesInM μs μInf ∧ ConvergesInM Ss SInf ∧
      MartOT.Var.IsShadow ν μInf SInf := by sorry

end MartOT.Shadow
