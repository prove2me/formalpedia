-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_13
-- name    : MartOT.Shadow.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:16.243766+00:00
-- url     : https://prove2.me/theorems/e6dd059d-2183-43ef-bf73-acd322921447
-- title:
--   Lemma 4.13, p. 28 — shadow of finitely many atoms: ν_n = ν_{n−1} + S^{ν−ν_{n−1}}(δ_n)
-- statement:
--   Let $(\delta_i)_{i\ge1}$ be atoms, $\delta_i=\alpha_i\,\delta_{x_i}$ at points $x_i\in\mathbb R$ with masses $\alpha_i\in[0,+\infty[$ (the weight $0$ is allowed), and let $\nu$ be a finite Borel measure on $\mathbb R$ with finite first moment. For $n\ge1$ put $\mu_n=\delta_1+\dots+\delta_n$ and assume $\mu_n\preceq_E\nu$ (extended convex order) for every $n\ge1$. Let $\mu_0=0$ (the empty sum) and $\nu_n=S^\nu(\mu_n)$ for $n\in\mathbb N$. Then $\nu_0=0$, and for every $n\ge1$ the shadow $S^{\nu-\nu_{n-1}}(\delta_n)$ exists and
--   $$\nu_n=\nu_{n-1}+S^{\nu-\nu_{n-1}}(\delta_n).$$
--
--   The shadow of a finitely atomic measure can thus be built one atom at a time, from left to right in the order of the labels.
--
--   **Formalization Note** The sequence $(\nu_n)$ is any sequence with $\nu_n$ a shadow of $\mu_n=\sum_{i=1}^n\delta_i$ in $\nu$ for every $n\in\mathbb N$ (so $\nu_0$ is a shadow of the zero measure, and $\nu_0=0$ is part of the conclusion, as on the page); the conclusion asserts the existence of a shadow $\sigma$ of $\delta_n$ in $\nu-\nu_{n-1}$ with $\nu_n=\nu_{n-1}+\sigma$, which with uniqueness of shadows (Lemma 4.6) is the recurrence. Masses are nonnegative reals (`ℝ≥0`). Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Lemma 4.13, p. 28

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem lemma_4_13 (x : ℕ → ℝ) (α : ℕ → ℝ≥0) (ν : Measure ℝ)
    (h : ∀ n, 1 ≤ n →
      MartOT.Var.ExtConvexLE (∑ i ∈ Finset.Icc 1 n, (α i : ENNReal) • Measure.dirac (x i)) ν)
    (νs : ℕ → Measure ℝ)
    (hS : ∀ n,
      MartOT.Var.IsShadow ν (∑ i ∈ Finset.Icc 1 n, (α i : ENNReal) • Measure.dirac (x i)) (νs n)) :
    νs 0 = 0 ∧
    ∀ n, 1 ≤ n → ∃ σ : Measure ℝ,
      MartOT.Var.IsShadow (ν - νs (n - 1)) ((α n : ENNReal) • Measure.dirac (x n)) σ ∧
      νs n = νs (n - 1) + σ := by sorry

end MartOT.Shadow
