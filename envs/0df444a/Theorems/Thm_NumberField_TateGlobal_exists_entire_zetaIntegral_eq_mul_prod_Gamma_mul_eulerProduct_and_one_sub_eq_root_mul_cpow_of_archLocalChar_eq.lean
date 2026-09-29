-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
-- name    : NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/84a366c9-0953-5e27-9a98-af5b9d59e92e
-- title:
--   Entire zeta integral and functional equation for Hecke characters
-- statement:
--   Let $K$ be a number field, $S$ a finite set of nonzero primes of $\mathcal O_K$, and $\rho=(\rho_v)_v$ a family of homomorphisms $(K_v)^\times\to\mathbb C^\times$ indexed by the finite places. Then there is a real $N_{\mathfrak f}>0$, depending only on $K$, $S$ and $\rho$, with the following property. Let $\chi:(\mathbb A_K)^\times\to\mathbb C^\times$ be a homomorphism which is continuous, unitary in the sense that $\|\chi(x)\|=1$ for all $x$, trivial on the image of $K^\times$, unramified at every $v\notin S$ (i.e. $\chi$ restricted to the local units at $v$, embedded in the ideles by $1$ outside $v$, is trivial on every $t$ with $t,t^{-1}$ integral), and such that for $v\in S$ this local restriction agrees with $\rho_v$ on all such $t$. Put $P(w)=\prod_v\bigl(1-c_v\,(\#(\mathcal O_K/v))^{-w}\bigr)^{-1}$, where $c_v=\chi(\varpi_v)$ for the idele $\varpi_v$ that is a uniformizer at $v$ and $1$ elsewhere when $\chi$ is unramified at $v$, and $c_v=0$ otherwise, and let $P'$ be the same product with $\chi(\varpi_v)^{-1}$ in place of $\chi(\varpi_v)$ (both as unconditional infinite products). Let $\tau:\mathrm{InfinitePlace}(K)\to\mathbb R$ and $m:\mathrm{InfinitePlace}(K)\to\mathbb Z$ be such that, at each infinite place $v$ and each unit $x$ of $K_v$ whose image in $\mathbb C$ has positive real part and zero imaginary part, the restriction of $\chi$ to the $v$-component equals $\|x\|_{\mathbb A}^{\,i\tau_v}$ (the idele norm being the module of the scaling action on the adeles), and whose image of absolute value $1$ gives $x^{m_v}$. Set $\gamma(s)=\prod_v\Gamma_{\mathbb R}(s+i\tau_v+(|m_v|\bmod 2))$ over the real places times $\prod_v\Gamma_{\mathbb C}(s+i\tau_v+|m_v|/2)$ over the complex places, and $\gamma'$ the same with $-i\tau_v$. The conclusion is twofold. First, if $\chi$ is not of the form $x\mapsto\|x\|^{i\tau_0}$ for any $\tau_0\in\mathbb R$, there are an entire $Z:\mathbb C\to\mathbb C$ and constants $A\neq0$, $\|\varepsilon\|=1$ with $Z(s)=A\,\gamma(s)P(s)$ and $Z(1-s)=A\varepsilon N_{\mathfrak f}^{\,s-1/2}\gamma'(s)P'(s)$ for all $\operatorname{Re}s>1$. Second, for every $\tau_0$ with $\chi(x)=\|x\|^{i\tau_0}$, there are such $Z$, $A\neq0$, $\|\varepsilon\|=1$ with $Z(s)=A\,(s+i\tau_0)\bigl(s-(1-i\tau_0)\bigr)\gamma(s)P(s)$ and $Z(1-s)=A\varepsilon N_{\mathfrak f}^{\,s-1/2}(s-i\tau_0)\bigl(s-(1+i\tau_0)\bigr)\gamma'(s)P'(s)$ for $\operatorname{Re}s>1$.
--
--   This is Tate's main theorem for Hecke characters in explicit form: the completed $L$-function attached to $\chi$ is realised, up to a nonzero constant, as an entire function satisfying a functional equation with conductor constant $N_{\mathfrak f}$ and root number of absolute value $1$, the norm-power characters being handled by inserting the two polar factors. The uniformity of $N_{\mathfrak f}$ in the family of characters ramified only inside $S$ with prescribed local data $\rho$ is what the later bounds on completed $L$-values and on intertwining integrals use.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq.lean

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

theorem NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ Nf : ℝ, 0 < Nf ∧
    ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (_hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (_hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
      (_hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
      (_hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρ v u),
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    let P' : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
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
    let γ' : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (s - ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))
    ((∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀) →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re → Z s = A * (γ s * P s)) ∧
        (∀ s : ℂ, 1 < s.re → Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) * (γ' s * P' s))) ∧
    (∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∃ (Z : ℂ → ℂ) (A ε : ℂ), Differentiable ℂ Z ∧ A ≠ 0 ∧ ‖ε‖ = 1 ∧
        (∀ s : ℂ, 1 < s.re →
          Z s = A * ((s + ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ s * P s)))) ∧
        (∀ s : ℂ, 1 < s.re →
          Z (1 - s) = A * ε * ((Nf : ℂ) ^ (s - 1 / 2)) *
            ((s - ((τ₀ : ℝ) : ℂ) * Complex.I) * ((s - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ' s * P' s))))) := by sorry
