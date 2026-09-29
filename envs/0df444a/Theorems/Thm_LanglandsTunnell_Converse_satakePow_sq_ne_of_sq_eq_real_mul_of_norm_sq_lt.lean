-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt
-- name    : LanglandsTunnell.Converse.satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ed316ff0-432a-523e-8d04-6da49d551b58
-- title:
--   Genericity of degree-f Satake power sums under a local bound
-- statement:
--   Let $a,b\in\mathbb{C}$, let $p$ be a natural number with $1<p$, and let $t\in\mathbb{R}$ with $t\ge 0$. Assume $a^{2}=t\,b$ (with $t$ regarded as a complex number) and the strict bound $\lVert a\rVert^{2}<\lVert b\rVert\,\bigl(p+2+p^{-1}\bigr)$, the right-hand side computed in $\mathbb{R}$ with $p^{-1}$ the ordinary inverse of the real number $p$. Let $f$ be a natural number with $f>0$. Write $\mathrm{satakePow}$ for the sequence in a commutative ring defined by $\mathrm{satakePow}_{0}(s,e)=2$, $\mathrm{satakePow}_{1}(s,e)=s$ and $\mathrm{satakePow}_{n+2}(s,e)=s\,\mathrm{satakePow}_{n+1}(s,e)-e\,\mathrm{satakePow}_{n}(s,e)$, i.e. the power sums of the roots of $X^{2}-sX+e$. Then $$\mathrm{satakePow}_{f}(a,b)^{2}\;\neq\;b^{f}\bigl(q+2+q^{-1}\bigr),$$ where $q=p^{f}$ is formed in $\mathbb{N}$ and then cast into $\mathbb{C}$, and $q^{-1}$ is its inverse in $\mathbb{C}$. Only $p\ge 2$ is assumed; no primality of $p$ enters.
--
--   In terms of the two roots $\alpha,\beta$ of $X^{2}-aX+b$, the excluded equality $(\alpha^{f}+\beta^{f})^{2}=(\alpha\beta)^{f}(q+2+q^{-1})$ says exactly that $(\alpha/\beta)^{f}=q^{\pm 1}$, the degeneracy condition for the unramified principal series with Satake parameters $\alpha^{f},\beta^{f}$ over a local field with residue cardinality $q=p^{f}$. It is used in the construction of a formal base change with generic local data, in [`LanglandsTunnell.Converse.exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable`](thm.html#LanglandsTunnell.Converse.exists_formalBaseChange_generic_of_isArithGenuineCuspRealizable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.Converse.satakePow_sq_ne_of_sq_eq_real_mul_of_norm_sq_lt
    (a b : ℂ) (p : ℕ) (hp : 1 < p)
    (t : ℝ) (ht0 : 0 ≤ t) (hat : a ^ 2 = (t : ℂ) * b)
    (hab : ‖a‖ ^ 2 < ‖b‖ * ((p : ℝ) + 2 + (p : ℝ)⁻¹))
    (f : ℕ) (hf : 0 < f) :
    AutomorphicForm.satakePow f a b ^ 2 ≠
      b ^ f * (((p ^ f : ℕ) : ℂ) + 2 + ((p ^ f : ℕ) : ℂ)⁻¹) := by sorry
