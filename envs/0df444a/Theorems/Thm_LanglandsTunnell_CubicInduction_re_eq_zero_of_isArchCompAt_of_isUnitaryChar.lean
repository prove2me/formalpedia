-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
-- name    : LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/6108d888-be4c-55ab-a246-75a14819cb6c
-- title:
--   Unitary idele class characters have purely imaginary archimedean exponent
-- statement:
--   Let $K$ be a number field, and let $\mu \colon (\mathbf{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $K$ (formed over $\mathcal{O}_K$) to $\mathbb{C}^\times$ which is unitary in the sense that $\lVert \mu(x) \rVert = 1$ for every idele $x$. Let $w$ be an infinite place of $K$, let $u \in \mathbb{C}$ and let $a \in \mathbb{Z}$, and suppose that $\mu$ has archimedean component of the stated shape at $w$ with exponents $(u,a)$: for every $x \in (K_w)^\times$, where $K_w$ is the completion of $K$ at $w$, the value of $\mu$ on the image of $x$ under the inclusion $(K_w)^\times \to (\mathbf{A}_K)^\times$ at the place $w$ equals $$\lVert x \rVert^{\,m_w u} \cdot \bigl(e_w(x)/\lVert x \rVert\bigr)^{a},$$ with $m_w$ the multiplicity of $w$ ($1$ for real, $2$ for complex), $e_w \colon K_w \to \mathbb{C}$ the canonical embedding of the completion, and the first factor a complex power of the real number $\lVert x \rVert$. The conclusion is that $\operatorname{Re}(u) = 0$.
--
--   This is the standard fact that, in the parametrisation $x \mapsto \lVert x\rVert^{m_w u}(e_w(x)/\lVert x\rVert)^a$ of the quasi-characters of $\mathbb{R}^\times$ and $\mathbb{C}^\times$, unitarity of the character forces the archimedean exponent to be purely imaginary. It is used to control the archimedean exponents of the twisting characters occurring in the archimedean zeta-function identities of the cubic induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 K) K μ)
    (w : InfinitePlace K) (u : ℂ) (a : ℤ) (h : IsArchCompAt K μ w u a) :
    u.re = 0 := by sorry
