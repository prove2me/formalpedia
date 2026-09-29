-- Prove2me | Theorems.Thm_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
-- name    : NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/616197a5-15ab-5fe8-8e05-7ca67902c97c
-- title:
--   Gaussian growth bound for (s-1)ζ_K(s) in vertical strips
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` structure over $\mathbb{Q}$), and let $R : \mathbb{C} \to \mathbb{C}$ be a function that is complex differentiable at every point, i.e. entire, and that satisfies $R(s) = (s-1)\,\zeta_K(s)$ for every $s$ with $\operatorname{Re} s > 1$, where $\zeta_K$ is `NumberField.dedekindZeta K`. Let $a$ and $b$ be arbitrary real numbers (no relation between them is assumed, so the assertion is vacuous when $a > b$). Then there exist real constants $B$ and $C$, depending on $K$, $R$, $a$ and $b$, such that for every $s \in \mathbb{C}$ with $a \le \operatorname{Re} s$ and $\operatorname{Re} s \le b$ one has $$\|R(s)\| \le B \exp\!\big(C \,(\operatorname{Im} s)^2\big).$$ Thus $R$ obeys a Gaussian bound, uniform on the closed vertical strip $a \le \operatorname{Re} s \le b$. No uniqueness of $R$ is asserted, and the bound obtained is weaker than the true polynomial growth of $(s-1)\zeta_K(s)$ in vertical strips.
--
--   This is the a priori growth estimate for the entire continuation of $(s-1)\zeta_K(s)$ that serves as the hypothesis of the Phragmén–Lindelöf principle, under which polynomial bounds on two vertical lines interpolate across the intervening strip. It is derived from the functional equation package for the completed Dedekind zeta function [`NumberField.exists_completedDedekindZeta_package`](thm.html#NumberField.exists_completedDedekindZeta_package), in particular from the order-one bound $\log\|\xi_K(s)\| \le C\|s\|\log\|s\|$, and it is used in the convexity estimates for partial Dedekind zeta functions in Tate's global theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
    (K : Type) [Field K] [NumberField K] (R : ℂ → ℂ) (hR : Differentiable ℂ R)
    (hRζ : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * NumberField.dedekindZeta K s) (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖R s‖ ≤ B * Real.exp (C * s.im ^ 2) := by sorry
