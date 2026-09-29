-- Prove2me | Theorems.Thm_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
-- name    : NumberField.exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/ca2912f9-022c-5462-9901-ca684235603f
-- title:
--   Polynomial bound for (s-1)ζ_K(s) on Re s=-1/2
-- statement:
--   Let $K$ be a number field, i.e. a field equipped with the `NumberField` structure. The assertion is that there exist real numbers $C$ and $A$, both strictly positive and depending only on $K$, with the following property: for every function $R \colon \mathbb{C} \to \mathbb{C}$ that is complex differentiable on all of $\mathbb{C}$ and satisfies $R(s) = (s-1)\,\zeta_K(s)$ for every $s$ with $\operatorname{Re} s > 1$, where $\zeta_K$ denotes `NumberField.dedekindZeta K`, and for every $s \in \mathbb{C}$ with $\operatorname{Re} s = -1/2$, one has $\lVert R(s) \rVert \le C\,(2 + \lvert \operatorname{Im} s \rvert)^{A}$, the exponentiation being the real power of the positive real number $2 + \lvert \operatorname{Im} s \rvert$. The quantifier order matters: the pair $(C, A)$ is chosen before $R$, so a single pair of constants serves all entire functions interpolating $(s-1)\zeta_K(s)$ on the half-plane $\operatorname{Re} s > 1$. Nothing is claimed here about the existence or uniqueness of such an $R$; the bound is asserted conditionally on one being given.
--
--   This is the functional-equation half of the convexity estimate for the Dedekind zeta function of $K$: on the line $\operatorname{Re} s = -1/2$ the completed zeta function reflects $\zeta_K$ to the absolutely convergent line $\operatorname{Re} s = 3/2$, and the ratio of archimedean Gamma factors grows at most polynomially in $\lvert \operatorname{Im} s\rvert$. It feeds the corresponding growth bound for partial Dedekind zeta functions on a vertical strip in the Tate-style global analytic package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
    (K : Type) [Field K] [NumberField K] :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (R : ℂ → ℂ), Differentiable ℂ R →
        (∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) →
      ∀ s : ℂ, s.re = -1 / 2 → ‖R s‖ ≤ C * (2 + |s.im|) ^ A := by sorry
