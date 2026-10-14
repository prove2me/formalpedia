-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_theorem_3_infconv
-- name    : LambdaVaRAmb.InfConv.theorem_3_infconv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:46.352391+00:00
-- url     : https://prove2.me/theorems/c57d3b43-5eed-44bb-810b-c7d83edd0200
-- title:
--   Theorem 3 (7) — the inf-convolution of risk measures induced by downsets is induced by 𝒜̃ₓ
-- statement:
--   Let $n\ge1$ and, for each $i\in[n]$, let $\{\mathcal A^{(i)}_x\}_{x\in\mathbb R}$ be a family of downsets of $\mathcal F$ with induced risk measure
--   $$
--   \rho_i(X)=\inf\{x\in\mathbb R:\{X>x\}\in\mathcal A^{(i)}_x\},\qquad X\in\mathcal X .
--   $$
--   If every $\rho_i$ takes values in $[-\infty,\infty)$ on $\mathcal X$, then for every $X\in\mathcal X$
--   $$
--   \mathop{\square}_{i=1}^n\rho_i(X)=\inf\{x\in\mathbb R:\{X>x\}\in\widetilde{\mathcal A}_x\},
--   $$
--   where $\widetilde{\mathcal A}_x$ is the union over $y_1+\dots+y_n=x$ of the sets $\{\bigcup_iA_i:A_i\in\mathcal A^{(i)}_{y_i}\}$.
--
--   So the class of risk measures induced by families of downsets is closed under inf-convolution.
--
--   **Formalization Note** The hypothesis $\rho_i<\infty$ is the theorem's own "$\rho_i:\mathcal X\to[-\infty,\infty)$"; it also keeps $+\infty$ and $-\infty$ from being added in the extended reals. $n\ge1$ is implicit in the paper ("$n$ agents"); for $n=0$ the identity fails. $\mathcal X$ is any domain satisfying the clauses of the setting file.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 15, Theorem 3, (6), (7)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem theorem_3_infconv {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (𝒜 : Fin n → ℝ → Set (Set Ω))
    (h𝒜 : ∀ i x, IsDownset (𝒜 i x)) (hfin : ∀ i, ∀ X ∈ dom, inducedRM (𝒜 i) X ≠ ⊤) :
    ∀ X ∈ dom, infConv dom (fun i => inducedRM (𝒜 i)) X = inducedRM (convFamily 𝒜) X := by sorry

end LambdaVaRAmb.InfConv
