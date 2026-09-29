-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
-- name    : NumberField.TateGlobal.exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/339fb1bc-36dd-5790-bf1a-f9566fa7d37d
-- title:
--   Bounded entire continuation of a unitary idele class L-function
-- statement:
--   Let $K$ be a number field, and let $\chi\colon (\mathbf{A}_K)^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$ which is an idele class character (it is trivial on the image of $K^\times$ under the diagonal embedding), is continuous, is unitary ($\lVert\chi(x)\rVert = 1$ for every idele unit $x$), and is non-trivial on the norm-one ideles, that is, on the kernel of the distributive Haar character of $\mathbf{A}_K$. Then there exist finite sets $S \subseteq S'$ of nonzero primes of $\mathcal{O}_K$, a natural number $m$, families $c, d\colon \mathrm{Fin}\,m \to \mathbb{C}$, functions $Z, D\colon \mathbb{C}\to\mathbb{C}$ and a constant $C_0 \neq 0$ with the following properties. The set $S$ consists exactly of those $v$ at which $\chi$ is ramified, in the sense that $v \in S$ iff the local character $t \mapsto \chi$ of the idele with $v$-component $t$ and all other components $1$ fails to be trivial on the units $t$ of $K_v$ with both $t$ and $t^{-1}$ in the valuation ring. All $c_j$ and all $d_j$ have non-negative real part. The function $Z$ is differentiable on all of $\mathbb{C}$, and for any $\sigma_1, \sigma_2 \in \mathbb{R}$ there is a constant bounding $\lVert Z(s)\rVert$ on the strip $\sigma_1 \le \operatorname{Re} s \le \sigma_2$. For $\operatorname{Re} s > 1$, $$Z(s) = C_0 \cdot \prod_j \Gamma_{\mathbb{R}}(s + c_j) \cdot \prod_{v \notin S} \bigl(1 - \chi(\varpi_v)\, N(v)^{-s}\bigr)^{-1},$$ where $\varpi_v$ is the idele which is a uniformiser at $v$ and $1$ at all other places including the infinite ones, $N(v)$ is the absolute norm of $v$, and the product is an unconditional infinite product over the primes outside $S$. Finally, for each $\sigma_2$ there is a bound for $\lVert D(s)\rVert$ on $1 \le \operatorname{Re} s \le \sigma_2$, and for $\operatorname{Re} s > 1$, $$Z(1-s) = D(s) \cdot \prod_j \Gamma_{\mathbb{R}}(s + d_j) \cdot \prod_{v \notin S'} \bigl(1 - \chi(\varpi_v)^{-1} N(v)^{-s}\bigr)^{-1}.$$
--
--   This is the global output of Tate's theory for a unitary idele class character that is non-trivial on the norm-one ideles: an entire completed $L$-function, bounded in vertical strips, whose Euler side over the unramified places is the finite-part Hecke $L$-series, together with a dual-side description of $Z(1-s)$. The second identity is weaker than the classical functional equation: the Euler product there is taken only over the places outside $S'$, and $D$ is asserted to be bounded on closed strips inside $\operatorname{Re} s \ge 1$, with no non-vanishing, root-number shape, or relation between the shifts $c_j$ and $d_j$. It is used by [`NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc`](thm.html#NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc), which extracts from it growth bounds for partial Euler products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

theorem
NumberField.TateGlobal.exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1) :
    ∃ (S S' : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (c d : Fin m → ℂ) (Z D : ℂ → ℂ) (C₀ : ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S ↔ ¬ IsUnramifiedCharAt χ v) ∧ S ⊆ S' ∧ C₀ ≠ 0 ∧
      (∀ j, 0 ≤ (c j).re) ∧ (∀ j, 0 ≤ (d j).re) ∧ Differentiable ℂ Z ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re →
        Z s = C₀ * (∏ j, Complex.Gammaℝ (s + c j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
            (1 - ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      (∀ σ₂ : ℝ, ∃ D₀ : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖D s‖ ≤ D₀) ∧
      (∀ s : ℂ, 1 < s.re →
        Z (1 - s) = D s * (∏ j, Complex.Gammaℝ (s + d j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S'},
            (1 - (((χ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) := by sorry
