-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
-- name    : NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/d6e107a4-88f0-5a3f-8702-4ac2ed57c0e4
-- title:
--   Entire continuation of Hecke L-functions with explicit Γ-factors
-- statement:
--   Let $K$ be a number field and $\chi\colon (\mathbb{A}_K^\times)\to\mathbb{C}^\times$ a group homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$ whose underlying $\mathbb{C}$-valued function is continuous, which is unitary ($\|\chi(x)\|=1$ for all $x$) and an idele class character (trivial on the ideles $\mathrm{diag}(u)$ coming from $u\in K^\times$). Put $P(w)=\prod_v\bigl(1-a_v\,(\mathrm{N}v)^{-w}\bigr)^{-1}$, the infinite product over the height-one primes $v$ of $\mathcal{O}_K$, where $\mathrm{N}v$ is the absolute norm of $v$ and $a_v=\chi(\varpi_v)$ — with $\varpi_v$ the idele that is a uniformizer at $v$ and $1$ elsewhere — if $\chi$ is unramified at $v$ (its $v$-component is trivial on those $t$ with $t$ and $t^{-1}$ both in the valuation ring), and $a_v=0$ otherwise. Let $\tau\colon\mathrm{InfinitePlace}(K)\to\mathbb{R}$ and $m\colon\mathrm{InfinitePlace}(K)\to\mathbb{Z}$ be such that, for every infinite place $v$ and every unit $x$ of $K_v$: if the image of $x$ under the embedding $K_v\hookrightarrow\mathbb{C}$ has positive real part and zero imaginary part, then $\chi$ evaluated at the idele equal to $x$ at $v$ and $1$ elsewhere equals $\|x\|_{\mathbb{A}}^{\,i\tau_v}$ (the idele module being the distinguished Haar character of $\mathbb{A}_K$); and if that image has absolute value $1$, the same value equals the $m_v$-th power of the image. Put $\gamma(s)=\prod_{v\ \mathrm{real}}\Gamma_{\mathbb{R}}(s+i\tau_v+(|m_v|\bmod 2))\cdot\prod_{v\ \mathrm{complex}}\Gamma_{\mathbb{C}}(s+i\tau_v+|m_v|/2)$. The conclusion is a conjunction: (i) if $\chi$ differs from $x\mapsto\|x\|_{\mathbb{A}}^{\,i\tau_0}$ for every $\tau_0\in\mathbb{R}$, then there are entire functions $L,\Lambda$ on $\mathbb{C}$ with $L(w)=P(w)$ for $\mathrm{Re}\,w>1$ and $\Lambda(s)=\gamma(s)L(s)$ for $\mathrm{Re}\,s>0$; (ii) for every $\tau_0\in\mathbb{R}$ with $\chi(x)=\|x\|_{\mathbb{A}}^{\,i\tau_0}$, there are entire $Q,\Lambda_Q$ with $Q(w)=(w-(1-i\tau_0))P(w)$ for $\mathrm{Re}\,w>1$ and $\Lambda_Q(s)=(s+i\tau_0)\,\gamma(s)Q(s)$ for $\mathrm{Re}\,s>0$.
--
--   This is the analytic continuation of Hecke $L$-functions and of their completions in the style of Tate's thesis, with the archimedean $\Gamma$-factors pinned down by the parameters $(\tau_v,m_v)$ read off from the local components of $\chi$; the two clauses separate the generic case from the norm-power characters, where a single pole forces the linear factor. It serves as the existence input for the explicit functional equation and for statements about completed $L$-functions attached to automorphic forms, in particular the bounds on intertwining integrals and Euler products that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq.lean

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

theorem NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq
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
    ((∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) →
      ∃ (L Λ : ℂ → ℂ), Differentiable ℂ L ∧ Differentiable ℂ Λ ∧
        (∀ w : ℂ, 1 < w.re → L w = P w) ∧ (∀ s : ℂ, 0 < s.re → Λ s = γ s * L s)) ∧
    (∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∃ (Q ΛQ : ℂ → ℂ), Differentiable ℂ Q ∧ Differentiable ℂ ΛQ ∧
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * P w) ∧
        (∀ s : ℂ, 0 < s.re → ΛQ s = (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * (γ s * Q s))) := by sorry
