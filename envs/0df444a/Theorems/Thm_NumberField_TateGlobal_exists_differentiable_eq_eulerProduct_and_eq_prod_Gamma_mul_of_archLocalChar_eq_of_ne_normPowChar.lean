-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
-- name    : NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/c33c0a24-436e-55ef-b5bd-fc9ee84410fb
-- title:
--   Entire L and Λ for non-norm-power idele class characters
-- statement:
--   Let $K$ be a number field and let $\chi\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring which is continuous as a complex-valued function, unitary in the sense that $\|\chi(x)\|=1$ for every idele $x$, and trivial on the principal ideles, i.e. $\chi$ composed with $K^\times \to \mathbb{A}_K^\times$ is the trivial character. Put $P(w) = \prod_v (1 - c_v\, (\mathrm{N}v)^{-w})^{-1}$, an infinite product over the finite places $v$ of $\mathcal{O}_K$, where $\mathrm{N}v$ is the absolute norm of the prime ideal $v$ and $c_v = \chi(\varpi_v)$ if $\chi$ is unramified at $v$ — meaning that the local character $t \mapsto \chi$ of the idele that is $t$ at $v$ and $1$ elsewhere is trivial on those units $t$ of the completion $K_v$ with $t$ and $t^{-1}$ both integral — and $c_v = 0$ otherwise; here $\varpi_v$ is the idele which is a uniformizer at $v$ and $1$ at all other places, finite and infinite. Fix further $\tau\colon$ (infinite places) $\to \mathbb{R}$ and $m\colon$ (infinite places) $\to \mathbb{Z}$ subject to two conditions describing $\chi$ at the archimedean places, where for an infinite place $v$ and a unit $x$ of $K_v$ one writes $\chi_v(x)$ for the value of $\chi$ on the idele that is $x$ at $v$ and $1$ elsewhere, and $x$ is embedded in $\mathbb{C}$ through the completion's embedding: firstly, if the embedded $x$ has positive real part and vanishing imaginary part then $\chi_v(x) = \|{\cdot}\|^{\,\tau_v i}$ evaluated at that idele, the norm being the module given by the scaling of additive Haar measure on $\mathbb{A}_K$; secondly, if the embedded $x$ has absolute value $1$ then $\chi_v(x)$ equals its $m_v$-th power. Put $\gamma(s) = \prod_v \Gamma_{\mathbb{R}}(s + \tau_v i + (|m_v| \bmod 2))$ over the real places times $\prod_v \Gamma_{\mathbb{C}}(s + \tau_v i + |m_v|/2)$ over the complex places. The assertion is: if $\chi$ is not equal to the character $x \mapsto \|x\|^{\,i\tau_0}$ for any real $\tau_0$, then there exist entire functions $L, \Lambda\colon \mathbb{C} \to \mathbb{C}$ with $L(w) = P(w)$ for $\operatorname{Re} w > 1$ and $\Lambda(s) = \gamma(s) L(s)$ for $\operatorname{Re} s > 0$.
--
--   This is the analytic continuation part of Tate's thesis for Hecke $L$-functions, in the case of a character that is not a pure power of the idele norm: both the Euler product and its completion by archimedean $\Gamma$-factors extend to entire functions (with ramified Euler factors read as $1$). It serves as the non-norm-power case of the general continuation statement [`NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq`](thm.html#NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq), which combines it with the complementary case where $\chi$ is a norm power and poles occur.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar.lean

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

theorem NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
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
    (∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) →
      ∃ (L Λ : ℂ → ℂ), Differentiable ℂ L ∧ Differentiable ℂ Λ ∧
        (∀ w : ℂ, 1 < w.re → L w = P w) ∧ (∀ s : ℂ, 0 < s.re → Λ s = γ s * L s) := by sorry
