-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
-- name    : NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/65cf8df8-04cd-5e68-a801-de86cf7265c6
-- title:
--   De la Vallée Poussin zero-free region for ζ_{K,T}
-- statement:
--   Let $K$ be a number field and let $T$ be a finite set of points of the height-one spectrum of the ring of integers $\mathcal{O}_K$, i.e. a finite set of nonzero prime ideals. The assertion is that there exists a real constant $c>0$ with the following property: for every function $Z:\mathbb{C}\to\mathbb{C}$ that is differentiable on all of $\mathbb{C}$ and satisfies $$Z(s)=(s-1)\prod_{v\notin T}\bigl(1-N(v)^{-s}\bigr)^{-1}\qquad\text{for all } s \text{ with }\operatorname{Re} s>1,$$ the product being the topological product over the subtype of height-one primes $v$ not lying in $T$ and $N(v)=\mathrm{absNorm}(v)$ the absolute ideal norm of $v$, one has $Z(s)\neq 0$ for every $s\in\mathbb{C}$ with $$1-\frac{c}{\log\bigl(2+|\operatorname{Im} s|\bigr)}\le \operatorname{Re} s.$$ The constant $c$ depends only on $K$ and $T$ and is produced before the quantification over $Z$; the entire function $Z$ is quantified universally, so no existence of a continuation is asserted here. In particular $Z(1)\neq 0$, and $Z$ has no zeros in the stated region, which includes the whole half-plane $\operatorname{Re} s\ge 1$.
--
--   This is the de la Vallée Poussin zero-free region for the Dedekind zeta function of $K$ with the Euler factors at the finite set $T$ removed, the pole at $s=1$ having been cleared by the factor $s-1$; the constant is not claimed to be effective and no exceptional-zero refinement is asserted. It is used, together with growth bounds for $(s-1)\zeta_{K,T}$ in a vertical strip, in [`NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq`](thm.html#NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im|) ≤ s.re → Z s ≠ 0 := by sorry
