-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_theorem_1_i
-- name    : LambdaVaRAmb.InfConv.theorem_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:57.244056+00:00
-- url     : https://prove2.me/theorems/52cbf83f-4b61-4816-944f-c084a2fec762
-- title:
--   Theorem 1 (i) — ρ = ΛVaR^w with Λ ∈ ℋ*_I iff ρ is induced by an increasing family of downsets
-- statement:
--   Let $\rho:\mathcal X\to[-\infty,\infty]$. The following are equivalent:
--
--   1. there exist an increasing $\Lambda:\mathbb R\to(0,1]$ (i.e. $\Lambda\in\mathcal H^*_I$) and a capacity $w$ such that $\rho(X)=\Lambda\mathrm{VaR}^w(X)$ for every $X\in\mathcal X$;
--   2. there exists an increasing family of downsets $\{\mathcal A_x\}_{x\in\mathbb R}$ such that
--   $$
--   \rho(X)=\inf\{x\in\mathbb R:\{X>x\}\in\mathcal A_x\}\qquad\text{for every }X\in\mathcal X .
--   $$
--
--   This representation lets questions about $\Lambda\mathrm{VaR}$ with increasing $\Lambda$ be answered at the level of families of events.
--
--   **Formalization Note** Both sides quantify over the same domain $\mathcal X$, and the pair $(\Lambda,w)$ (resp. the family) is chosen once, uniformly in $X$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 10, Theorem 1 (i)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem theorem_1_i {Ω : Type*} [MeasurableSpace Ω] (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (ρ : (Ω → ℝ) → EReal) :
    (∃ Λ : ℝ → ℝ, InHStarI Λ ∧ ∃ w : Set Ω → ℝ, LambdaVaRAmb.Robust.IsCapacity w ∧ ∀ X ∈ dom, ρ X = LambdaVaRAmb.Robust.LVaR Λ w X) ↔
      (∃ 𝒜 : ℝ → Set (Set Ω), (∀ x, IsDownset (𝒜 x)) ∧ Monotone 𝒜 ∧
        ∀ X ∈ dom, ρ X = inducedRM 𝒜 X) := by sorry

end LambdaVaRAmb.InfConv
