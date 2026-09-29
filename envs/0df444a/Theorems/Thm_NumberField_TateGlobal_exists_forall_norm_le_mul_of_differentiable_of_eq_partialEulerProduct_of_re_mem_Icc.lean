-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
-- name    : NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c46e3955-06a2-58cc-89b1-79c7f92cd666
-- title:
--   Polynomial growth of partial Hecke L-functions on vertical strips
-- statement:
--   Let $K$ be a number field and let $\chi$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^{\times}$ which is an idele class character (trivial on the image of $K^{\times}$), is continuous, is unitary (so $\lVert\chi(x)\rVert = 1$ for every idele unit $x$), and is non-trivial on the norm-one ideles, meaning that some $x$ in the kernel of the module character `distribHaarChar` of the adele ring satisfies $\chi(x) \neq 1$. Let $T$ be a finite set of finite places of $K$, i.e. of height one primes of $\mathcal{O}_K$, let $\sigma_1, \sigma_2$ be real numbers, and let $L : \mathbb{C} \to \mathbb{C}$ be differentiable on all of $\mathbb{C}$ and such that for every $s$ with $\operatorname{Re} s > 1$ the value $L(s)$ equals the infinite product, over the finite places $v \notin T$, of $\bigl(1 - c_v \,\mathrm{N}(v)^{-s}\bigr)^{-1}$, where $\mathrm{N}(v)$ is the absolute norm of the prime ideal of $v$, and where $c_v = \chi(\text{uniformiser idele at } v)$ — the idele which is $1$ at the infinite places and at all finite places other than $v$, and a uniformiser at $v$ — whenever $\chi$ is unramified at $v$, in the sense that the local component of $\chi$ at $v$ is trivial on every unit of the completion at $v$ whose value and inverse both lie in the valuation ring, and $c_v = 0$ otherwise. The conclusion is that there exist a real number $A$ and a natural number $N$ with $\lVert L(w)\rVert \le A\,(1 + \lvert \operatorname{Im} w\rvert)^{N}$ for every $w$ satisfying $\sigma_1 \le \operatorname{Re} w \le \sigma_2$.
--
--   This is the statement that the finite (partial) Hecke $L$-function attached to a non-trivial continuous unitary idele class character, once analytically continued to an entire function, has at most polynomial growth in the imaginary direction on every vertical strip; the set $T$ of discarded places is arbitrary, so finitely many Euler factors may be removed or retained. It is used in the analytic input to the study of adelic automorphic forms, being cited in the construction of polynomially bounded Euler-product continuations for induced sections and in the complementary lower-bound statement for such $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (L : ℂ → ℂ) (_hL : Differentiable ℂ L)
    (_hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖L w‖ ≤ A * (1 + |w.im|) ^ N := by sorry
