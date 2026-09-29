-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/89ec9c9f-0d94-5f89-b79f-6c90a5d43546
-- title:
--   Dual section of the GL₂ principal series
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the $p$-adic completion, and let $\chi = (\chi_0,\chi_1)$ be a pair of multiplicative characters $F^\times \to \mathbb{C}^\times$. Let $f : \mathrm{GL}_2(F) \to \mathbb{C}$ belong to `principalSeries2 p χ`, i.e. $f$ is locally constant, satisfies $f\big(\binom{1\ x}{0\ 1} g\big) = f(g)$ for all $x \in F$ and all $g$, and satisfies $f(\mathrm{diag}(a_0,a_1)\,g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\;f(g)$ for all $a_0,a_1 \in F^\times$ and all $g$. Let $w_0 \in \mathrm{GL}_2(F)$ be an element whose underlying matrix is $!![0,1;1,0]$. The assertion is that there exists a pair $\chi' = (\chi'_0,\chi'_1)$ of characters $F^\times \to \mathbb{C}^\times$ such that, for every $a \in F^\times$, $\chi'_0(a) = \chi_1(a)^{-1}\,\mathrm{modulus}(a)$ and $\chi'_1(a) = \chi_0(a)^{-1}\,\mathrm{modulus}(a)$, where $\mathrm{modulus}(a)$ is the value of the distributive Haar character of $F$ at $a$ (equal to $\|a\|$, by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm)), and such that the function $h \mapsto \mathrm{modulus}(\det h)\, f\big(w_0 \cdot {}^{t}(h^{-1})\big)$, with ${}^{t}(h^{-1})$ the [`AutomorphicForm.transposeInvN`](def/AutomorphicForm_SmoothingKernel.html#L28) of $h$, lies in `principalSeries2 p χ'`.
--
--   This is the standard passage to the dual (contragredient) section $f^D(h) = |\det h|\,f(w_0\,{}^{t}h^{-1})$ of a normalised principal series of $\mathrm{GL}_2$ over a $p$-adic field, identifying the target as the principal series attached to $(\chi_1^{-1}|\cdot|,\chi_0^{-1}|\cdot|)$. It is used so that the convergence and unfolding results established for sections of a principal series apply on the dual side of the local Rankin–Selberg integrals for $\mathrm{GL}_3 \times \mathrm{GL}_2$, and is cited in the construction of dual middle data and in the local Rankin–Selberg integral identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_modulus_det_mul_apply_antidiagonal_mul_transposeInvN_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∃ χ' : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ),
      (∀ a : (p.adicCompletion ℚ)ˣ,
        ((χ' 0 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ)) ∧
      (∀ a : (p.adicCompletion ℚ)ˣ,
        ((χ' 1 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ)⁻¹ * (((modulus (a : p.adicCompletion ℚ) : ℝ)) : ℂ)) ∧
      (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) : ℂ) *
          f (w₀ * AutomorphicForm.transposeInvN (Fin 2) h)) ∈ principalSeries2 p χ' := by sorry
