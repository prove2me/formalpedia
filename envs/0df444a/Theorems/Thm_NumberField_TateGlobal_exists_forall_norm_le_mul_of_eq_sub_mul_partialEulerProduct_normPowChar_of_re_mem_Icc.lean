-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
-- name    : NumberField.TateGlobal.exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/1263af76-c2e9-557e-ba86-64006abdd49d
-- title:
--   Polynomial vertical-strip bound for a regularised partial zeta function
-- statement:
--   Let $K$ be a number field, $\tau$ a real number, $T$ a finite set of height-one primes of $\mathcal{O}_K$, and $\sigma_1,\sigma_2$ real numbers. Let $Q\colon\mathbb{C}\to\mathbb{C}$ be differentiable on all of $\mathbb{C}$ and suppose that for every $s$ with $\operatorname{Re} s>1$ one has $$Q(s)=\bigl(s-(1-i\tau)\bigr)\prod_{v\notin T}\bigl(1-c_v\,(\mathrm{N}v)^{-s}\bigr)^{-1},$$ the unordered product being taken over the finite places $v$ of $K$ outside $T$, where $\mathrm{N}v=\mathrm{absNorm}$ of the ideal of $v$, and where $c_v$ is the value of `normPowChar K τ` at the idele `uniformizerIdele K v` when that character is unramified at $v$, and $c_v=0$ otherwise. Here `normPowChar K τ` is the character sending an idele unit $x$ to $\lVert x\rVert^{i\tau}$, with $\lVert x\rVert$ the scaling factor of multiplication by $x$ on the adele ring of $K$ (its `distribHaarChar`); `uniformizerIdele K v` is the idele that is $1$ at the infinite places and at every finite place other than $v$ and a uniformiser of $K_v$ at $v$; and unramifiedness at $v$ means that the induced character of $K_v^\times$ is trivial on those units lying, together with their inverses, in the valuation ring of $K_v$. The conclusion is that there exist a real number $A$ and a natural number $N$ such that $\lVert Q(w)\rVert\le A\,(1+\lvert\operatorname{Im} w\rvert)^N$ for all $w$ with $\sigma_1\le\operatorname{Re} w\le\sigma_2$.
--
--   The hypothesised Euler product is, for $\operatorname{Re} s>1$, the Dedekind zeta function of $K$ at $s+i\tau$ with the factors at the places of $T$ removed, and the factor $s-(1-i\tau)$ cancels its simple pole; the assertion is the standard polynomial growth of this regularised partial zeta function on each vertical strip, obtained from the functional equation together with Stirling-type bounds for the Gamma factors. It feeds the growth estimates used in the analytic continuation of the relevant $L$-functions and Euler products, and is cited in particular by the polynomial-bound statement for Euler products attached to induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
    (K : Type) [Field K] [NumberField K] (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
    (_hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖Q w‖ ≤ A * (1 + |w.im|) ^ N := by sorry
