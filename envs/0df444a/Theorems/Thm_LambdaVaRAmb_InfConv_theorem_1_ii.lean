-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_theorem_1_ii
-- name    : LambdaVaRAmb.InfConv.theorem_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:57.836048+00:00
-- url     : https://prove2.me/theorems/d427b4cb-21a4-44dc-a982-c87fdf41eaa0
-- title:
--   Theorem 1 (ii) — ρ = ΛVaR^w with left-continuous Λ ∈ ℋ*_D iff ρ is induced by a decreasing left-continuous family of downsets
-- statement:
--   Let $\rho:\mathcal X\to[-\infty,\infty]$. The following are equivalent:
--
--   1. there exist a decreasing, left-continuous $\Lambda:\mathbb R\to(0,1]$ (i.e. a left-continuous $\Lambda\in\mathcal H^*_D$) and a capacity $w$ such that $\rho(X)=\Lambda\mathrm{VaR}^w(X)$ for every $X\in\mathcal X$;
--   2. there exists a decreasing family of downsets $\{\mathcal A_x\}_{x\in\mathbb R}$, left-continuous in the sense $\bigcap_{y<x}\mathcal A_y=\mathcal A_x$ for all $x$, such that
--   $$
--   \rho(X)=\inf\{x\in\mathbb R:\{X>x\}\in\mathcal A_x\}\qquad\text{for every }X\in\mathcal X .
--   $$
--
--   This is the decreasing counterpart of part (i).
--
--   **Formalization Note** Left-continuity of $\Lambda$ at $x$ is continuity of $\Lambda$ restricted to $(-\infty,x]$. Both sides quantify over the same domain $\mathcal X$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 10, Theorem 1 (ii)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem theorem_1_ii {Ω : Type*} [MeasurableSpace Ω] (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (ρ : (Ω → ℝ) → EReal) :
    (∃ Λ : ℝ → ℝ, InHStarD Λ ∧ (∀ x, ContinuousWithinAt Λ (Set.Iic x) x) ∧
        ∃ w : Set Ω → ℝ, LambdaVaRAmb.Robust.IsCapacity w ∧ ∀ X ∈ dom, ρ X = LambdaVaRAmb.Robust.LVaR Λ w X) ↔
      (∃ 𝒜 : ℝ → Set (Set Ω), (∀ x, IsDownset (𝒜 x)) ∧ Antitone 𝒜 ∧ IsLeftContFamily 𝒜 ∧
        ∀ X ∈ dom, ρ X = inducedRM 𝒜 X) := by sorry

end LambdaVaRAmb.InfConv
