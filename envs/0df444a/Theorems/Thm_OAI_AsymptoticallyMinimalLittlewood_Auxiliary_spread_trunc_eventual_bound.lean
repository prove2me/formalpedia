-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_spread_trunc_eventual_bound
-- name    : OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:10:59.043446+00:00
-- url     : https://prove2.me/theorems/e8c1e35f-f887-46d6-9a00-0d7c57e1ac15
-- title:
--   Truncated Fourier spreading of the binary polynomial is eventually bounded by $1+\delta$
-- statement:
--   Notation. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$. For $s\in\mathbb{Z}^n$ and $y\in\mathbb{T}^n$ write $e_s(y)=\prod_{k=1}^{n}e^{2\pi i s_k y_k}$, and for $b\in\mathbb{R}^n$ write $\langle s,b\rangle=\sum_{k}s_kb_k$. The binary polynomials $\Phi_n:\mathbb{T}^n\to\mathbb{R}$ are defined recursively by $\Phi_0=0$ and $\Phi_{n+1}(x_0,x_1,\dots,x_n)=\Phi_n(x_1,\dots,x_n)+\tfrac12\bigl(1-\Phi_n(x_1,\dots,x_n)^2\bigr)\cos(2\pi x_0)$. For $g:\mathbb{R}\to\mathbb{R}$ and real $B,\beta$, the truncated chirp row is the trigonometric polynomial
--   $$
--   R_{B,\beta}(\zeta)=\sum_{w\in\mathbb{Z},\ |w|\le B|\beta|/2}\Bigl(\int_{\mathbb{R}}g(x)\,e^{2\pi i(B\beta x^2/2-wx)}\,dx\Bigr)e^{2\pi i w\zeta},\qquad \zeta\in\mathbb{T}.
--   $$
--
--   Hypotheses. Let $n\ge0$, let $J$ be a finite index set, let $S\subset\mathbb{Z}^n$ be finite and let $c:\mathbb{Z}^n\to\mathbb{C}$ be such that
--   $$
--   \Phi_n(y)=P(y)+\overline{P(y)},\qquad P(y)=\sum_{s\in S}c(s)\,e_s(y),\qquad\text{for all } y\in\mathbb{T}^n .
--   $$
--   Let $g:\mathbb{R}\to\mathbb{R}$ be infinitely differentiable with compact support and $0\le g\le1$, and let $0\le\alpha<\tfrac12$ be such that the closed support of $g$ is contained in $[-\alpha,\alpha]$. Let $b_j\in\mathbb{R}^n$ ($j\in J$) be vectors with $\langle s,b_j\rangle\ne0$ for all $s\in S$ and $j\in J$, and let $\delta>0$.
--
--   Conclusion. There is $B_0$ such that for every real $B\ge B_0$, every $y\in\mathbb{T}^n$ and every $z=(z_j)_{j\in J}\in\mathbb{T}^J$,
--   $$
--   \bigl|Q_B(y,z)+\overline{Q_B(y,z)}\bigr|\le1+\delta,\qquad Q_B(y,z)=\sum_{s\in S}c(s)\,e_s(y)\prod_{j\in J}R_{B,\langle s,b_j\rangle}(z_j).
--   $$
--
--   The function $Q_B+\overline{Q_B}=2\operatorname{Re}Q_B$ is a real trigonometric polynomial on $\mathbb{T}^n\times\mathbb{T}^J$ obtained from $\Phi_n=2\operatorname{Re}P$ by spreading each frequency $s$: the character $e_s(y)$ is multiplied by a product of truncated chirp rows in the new variables $z_j$, with curvatures $B\langle s,b_j\rangle$. Since $|\Phi_n|\le1$, the theorem says that this spreading increases the supremum norm by at most the factor $1+\delta$ once the scale $B$ is large. It is the flatness half of the construction of the auxiliary Fourier packet.
--
--   **Formalization Note** $\Phi_n$ is `binary n`, $e_s$ is Mathlib's `mFourier s`, $\langle s,b\rangle$ is the linear form `rowForm s` applied to $b$, and $R_{B,\beta}$ is `rowTrunc` applied to $g$ viewed as a complex-valued function. "For all sufficiently large $B$" is expressed by the filter `Filter.Eventually` along `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Spreading.lean#L380-L440

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
universe uI uE uJ uK
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

theorem OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound {n : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s∈S, c s*mFourier s y)+conj (∑ s∈S, c s*mFourier s y))
    {g : ℝ → ℝ} (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg : ∀ x, 0≤g x ∧ g x≤1) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hga : tsupport g ⊆ Set.Icc (-α) α)
    (b : J → Fin n → ℝ) (hb : ∀ s∈S, ∀ j, rowForm s (b j)≠0)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ B : ℝ in atTop, ∀ y : Fin n → UnitAddCircle, ∀ z : J → UnitAddCircle,
      ‖(∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))+
        conj (∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))‖ ≤ 1+δ := by sorry
