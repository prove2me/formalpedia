-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
-- name    : NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4f76b464-6909-5560-a414-8e7b7ae9ef49
-- title:
--   Convexity bound for (s-1)ζ_{K,T} in a vertical strip
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $T$ be a finite set of height-one primes of $\mathcal{O}_K$. The assertion is that there exist real constants $C$ and $A$, both strictly positive, with the following property: for every function $Z \colon \mathbb{C} \to \mathbb{C}$ which is differentiable at every point of $\mathbb{C}$ and which satisfies, for all $s$ with $\operatorname{Re} s > 1$, $$Z(s) = (s-1)\prod_{v \notin T} \bigl(1 - N(v)^{-s}\bigr)^{-1},$$ the product being the unrestricted topological product over the subtype of height-one primes $v$ of $\mathcal{O}_K$ not lying in $T$ and $N(v)$ denoting the absolute norm $\mathrm{Ideal.absNorm}$ of the corresponding ideal, one has $$\lVert Z(s)\rVert \le C\,(2 + |\operatorname{Im} s|)^{A}$$ for every $s$ with $-1/2 \le \operatorname{Re} s \le 5/2$. The constants are thus uniform in $Z$ but may depend on $K$ and on $T$; the existence of such a $Z$ is not part of the statement.
--
--   This is the convexity (Phragmén–Lindelöf) growth bound for the partial Dedekind zeta function of $K$ with the Euler factors at $T$ removed, multiplied by $s-1$ to cancel the pole at $s=1$, valid in the closed strip $-1/2 \le \operatorname{Re} s \le 5/2$. It supplies the growth input for the de la Vallée-Poussin type zero-free regions for Hecke $L$-functions, and is used in the proofs of the non-vanishing statements for continuations of partial Euler products near the line $\operatorname{Re} s = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖Z s‖ ≤ C * (2 + |s.im|) ^ A := by sorry
