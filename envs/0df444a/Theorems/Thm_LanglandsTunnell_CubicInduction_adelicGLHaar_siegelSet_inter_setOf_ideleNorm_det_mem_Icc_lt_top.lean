-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
-- name    : LanglandsTunnell.CubicInduction.adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e8d0bbd8-9e36-57e9-af46-6ba2026a7470
-- title:
--   Finite Haar measure of a GL₃(A_ℚ) Siegel set slab
-- statement:
--   Let $c$, $C$, $a$, $b$ be real numbers with $0 < c$, $0 < a$ and $a < b$. Consider the subset of $\mathrm{GL}_3$ over the adele ring of $\mathbb{Q}$ consisting of those $g$ that admit a factorisation $g = n\,t\,k$ such that: at every finite place $p$ (every height-one prime of $\mathcal{O}_{\mathbb{Q}}$) the components of $n$ and of $t$ are the identity, while the component of $k$ lies in `localMaximalCompact3`, the subgroup of $\mathrm{GL}_3$ over the $p$-adic completion whose elements have all entries of the matrix and of its inverse of valuation at most $1$; and at every infinite place $w$ of $\mathbb{Q}$ the component of $n$ in $\mathrm{GL}_3$ over the completion at $w$ has all diagonal entries equal to $1$, vanishing entries $i j$ with $j < i$, and all entries of norm at most $C$, the component of $t$ has vanishing off-diagonal entries, the two real quantities `archRoot₁ ℚ w t` and `archRoot₂ ℚ w t` attached to $t$ at $w$ are both at least $c$, and the component $\kappa$ of $k$ satisfies $\kappa^{\mathsf{T}}\kappa = 1$. Intersect this set with the set of $g$ whose determinant, an idele, has `ideleNorm` (the real value of the distributive Haar character of the adele ring at that idele) lying in $[a,b]$. The assertion is that the Haar measure `adelicGLHaar` of $\mathrm{GL}_3$ over the adeles, for the Borel structure, assigns this intersection a value $< \infty$.
--
--   This is the finite-volume half of reduction theory for $\mathrm{GL}_3$ over $\mathbb{Q}$ in adelic form (Siegel, Borel–Harish-Chandra), with the central direction cut off by a compact determinant slab $a \le |\det g|_{\mathbb{A}} \le b$ instead of by passing to the quotient by the centre. It supports the $L^2$ estimates on such slabs in the cubic-induction part of the argument, in particular the construction of smoothing kernels and the Whittaker expansions attached to them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
    (c C : ℝ) (_hc : 0 < c) (a b : ℝ) (_ha : 0 < a) (_hab : a < b) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
        ({g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} ∩
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) < ⊤ := by sorry
