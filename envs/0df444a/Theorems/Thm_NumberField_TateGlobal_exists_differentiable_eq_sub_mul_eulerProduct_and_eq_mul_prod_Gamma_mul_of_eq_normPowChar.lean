-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
-- name    : NumberField.TateGlobal.exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/2d358310-4e74-534e-a631-509b4ec3edea
-- title:
--   Entire continuation of the completed zeta for norm-power characters
-- statement:
--   Let $K$ be a number field and let $\chi\colon (\mathbb{A}_K^\times) \to \mathbb{C}^\times$ be a homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$, assumed continuous as a $\mathbb{C}$-valued function, unitary ($\|\chi(x)\|=1$ for all $x$) and trivial on the principal ideles (i.e. $\chi$ kills the image of $K^\times$). Put $P(w)=\prod'_v\bigl(1-c_v(\chi)\,N(v)^{-w}\bigr)^{-1}$, the product over the finite places $v$ of $\mathcal{O}_K$, where $c_v(\chi)=\chi(\varpi_v)$ if $\chi$ is unramified at $v$ — meaning that $\chi$, restricted along the embedding of $(K_v)^\times$ as ideles trivial away from $v$, is $1$ on all $t$ with $t$ and $t^{-1}$ integral — and $c_v(\chi)=0$ otherwise; here $\varpi_v$ is the idele given by a uniformizer at $v$ and $1$ elsewhere, and $N(v)$ is the absolute norm of $v$. Let $\tau\colon \mathrm{InfinitePlace}(K)\to\mathbb{R}$ and $m\colon \mathrm{InfinitePlace}(K)\to\mathbb{Z}$ be such that, for every infinite place $v$ and every unit $x$ of $K_v$: if the image of $x$ in $\mathbb{C}$ is positive real then $\chi$ of the idele concentrated at $v$ with entry $x$ equals $\|x\|_{\mathrm{idele}}^{\,i\tau_v}$, the idele norm being the modulus of the Haar scaling character; and if that image has absolute value $1$ then the same value equals its $m_v$-th power. Set $$\gamma(s)=\prod_{v\ \mathrm{real}}\Gamma_{\mathbb{R}}\bigl(s+i\tau_v+(|m_v| \bmod 2)\bigr)\prod_{v\ \mathrm{complex}}\Gamma_{\mathbb{C}}\bigl(s+i\tau_v+|m_v|/2\bigr).$$ The assertion is: for every $\tau_0\in\mathbb{R}$, if $\chi$ is the norm power $x\mapsto \|x\|_{\mathrm{idele}}^{\,i\tau_0}$, then there exist entire functions $Q$ and $\Lambda_Q$ on $\mathbb{C}$ with $Q(w)=\bigl(w-(1-i\tau_0)\bigr)P(w)$ for $\operatorname{Re} w>1$ and $\Lambda_Q(s)=(s+i\tau_0)\,\gamma(s)\,Q(s)$ for $\operatorname{Re} s>0$.
--
--   This is the norm-power case of the analytic continuation in Tate's global theory: for $\chi=\|\cdot\|^{i\tau_0}$ the Euler product is the shifted Dedekind zeta function $\zeta_K(w+i\tau_0)$, whose simple pole at $w=1-i\tau_0$ is removed by the factor $w-(1-i\tau_0)$, while the factor $s+i\tau_0$ removes the pole of the completed zeta function at $s=-i\tau_0$ from the region $\operatorname{Re}s>0$. It supplies one of the two cases in the general statement [`NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq`](thm.html#NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq), which provides entire continuations of completed Hecke $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.exists_differentiable_eq_sub_mul_eulerProduct_and_eq_mul_prod_Gamma_mul_of_eq_normPowChar
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (_hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (_hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ) :
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    ∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
      (_hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
      (_hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)),
    let γ : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    ∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∃ (Q ΛQ : ℂ → ℂ), Differentiable ℂ Q ∧ Differentiable ℂ ΛQ ∧
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * P w) ∧
        (∀ s : ℂ, 0 < s.re → ΛQ s = (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * (γ s * Q s)) := by sorry
