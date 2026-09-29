-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
-- name    : NumberField.TateGlobal.exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/7994b7eb-4f1e-54c1-9e48-22e56704a6d2
-- title:
--   Hecke–Tate functional equation with pinned local data
-- statement:
--   Let $K$ be a number field, $S$ a finite set of nonzero primes of $\mathcal O_K$, and $\rho=(\rho_v)$ a family of homomorphisms $(K_v)^\times\to\mathbb C^\times$. The assertion is that there is a real $N_{\mathfrak f}>0$, depending only on $K$, $S$ and $\rho$, with the following property. Let $\chi\colon(\mathbb A_K)^\times\to\mathbb C^\times$ be a homomorphism whose composite with $\mathbb C^\times\hookrightarrow\mathbb C$ is continuous, which satisfies $\|\chi(x)\|=1$ for all $x$ and $\chi=1$ on the ideles coming from $K^\times$, which is unramified at every $v\notin S$ in the sense that $\chi$ is trivial on the ideles $\mathrm{localUnit}$ at $v$ attached to units $t$ of $K_v$ with $t,t^{-1}$ integral, and which on those units at $v\in S$ agrees with $\rho_v$. Put $P(w)=\prod_v(1-a_v N(v)^{-w})^{-1}$ and $P'(w)=\prod_v(1-a_v^{-1}N(v)^{-w})^{-1}$, where $a_v=\chi(\mathrm{uniformizerIdele}\,v)$ if $\chi$ is unramified at $v$ and $a_v$ is replaced by $0$ otherwise, and $N(v)=\mathrm{Ideal.absNorm}\,v$. Let $\tau\colon\Sigma_\infty\to\mathbb R$ and $m\colon\Sigma_\infty\to\mathbb Z$ be such that, for each infinite place $v$ and each unit $x$ of $K_v$, $\chi$ composed with the embedding of $(K_v)^\times$ into the ideles (trivial away from $v$) equals $\mathrm{ideleNorm}(x)^{i\tau_v}$ when the image of $x$ in $\mathbb C$ is real and positive, and equals $x^{m_v}$ when that image has absolute value $1$. Set $\gamma(s)=\prod_{v\ \mathrm{real}}\Gamma_{\mathbb R}(s+i\tau_v+(|m_v|\bmod 2))\prod_{v\ \mathrm{complex}}\Gamma_{\mathbb C}(s+i\tau_v+|m_v|/2)$ and let $\gamma'$ be the same with $\tau$ replaced by $-\tau$. Then two statements hold. First, if $\chi$ is not the character $x\mapsto \mathrm{ideleNorm}(x)^{i\tau_0}$ for any $\tau_0\in\mathbb R$, then for all entire $L,L'$ with $L=P$ and $L'=P'$ on $\operatorname{Re}w>1$ and all entire $\Lambda,\Lambda^{\vee}$ with $\Lambda=\gamma L$ and $\Lambda^{\vee}=\gamma' L'$ on $\operatorname{Re}s>0$, there is $\varepsilon$ with $\|\varepsilon\|=1$ and $\Lambda^{\vee}(1-s)=\varepsilon N_{\mathfrak f}^{\,s-1/2}\Lambda(s)$ for every $s\in\mathbb C$. Second, if $\chi=\mathrm{normPowChar}\,\tau_0$, the same conclusion holds with the pole removed: for all entire $Q,Q'$ with $Q(w)=(w-(1-i\tau_0))P(w)$ and $Q'(w)=(w-(1+i\tau_0))P'(w)$ on $\operatorname{Re}w>1$ and all entire $\Lambda_Q,\Lambda_Q^{\vee}$ with $\Lambda_Q(s)=(s+i\tau_0)\gamma(s)Q(s)$ and $\Lambda_Q^{\vee}(s)=(s-i\tau_0)\gamma'(s)Q'(s)$ on $\operatorname{Re}s>0$, there is $\varepsilon$ of modulus $1$ with $\Lambda_Q^{\vee}(1-s)=\varepsilon N_{\mathfrak f}^{\,s-1/2}\Lambda_Q(s)$ for all $s$.
--
--   This is the functional equation of Hecke for the completed $L$-function of a unitary idele class character, in the shape coming from Tate's local–global zeta integrals: the completed functions are taken as hypothesis objects, entire on all of $\mathbb C$ and required to agree with $\gamma\cdot L$ only on $\operatorname{Re}s>0$ where the archimedean factors have no poles, and the discriminant–conductor constant $N_{\mathfrak f}$ is uniform over all characters with the given ramification data. It is obtained from the corresponding statement about Tate zeta integrals, and is used in bounding the analytic continuation of Weyl intertwining integrals along vertical lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq.lean

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

theorem NumberField.TateGlobal.exists_forall_prod_Gamma_mul_eulerProduct_one_sub_eq_mul_cpow_mul_of_archLocalChar_eq
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
      ∀ (L : ℂ → ℂ), Differentiable ℂ L → (∀ w : ℂ, 1 < w.re → L w = P w) →
      ∀ (L' : ℂ → ℂ), Differentiable ℂ L' → (∀ w : ℂ, 1 < w.re → L' w = P' w) →
      ∀ (Λ Λd : ℂ → ℂ), Differentiable ℂ Λ → Differentiable ℂ Λd →
        (∀ s : ℂ, 0 < s.re → Λ s = γ s * L s) → (∀ s : ℂ, 0 < s.re → Λd s = γ' s * L' s) →
        ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s : ℂ, Λd (1 - s) = ε * ((Nf : ℂ) ^ (s - 1 / 2)) * Λ s) ∧
    (∀ τ₀ : ℝ, χ = normPowChar K τ₀ →
      ∀ (Q : ℂ → ℂ), Differentiable ℂ Q → (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * P w) →
      ∀ (Q' : ℂ → ℂ), Differentiable ℂ Q' → (∀ w : ℂ, 1 < w.re → Q' w = (w - ((1 : ℂ) + ((τ₀ : ℝ) : ℂ) * Complex.I)) * P' w) →
      ∀ (ΛQ ΛQd : ℂ → ℂ), Differentiable ℂ ΛQ → Differentiable ℂ ΛQd →
        (∀ s : ℂ, 0 < s.re → ΛQ s = (s + ((τ₀ : ℝ) : ℂ) * Complex.I) * (γ s * Q s)) →
        (∀ s : ℂ, 0 < s.re → ΛQd s = (s - ((τ₀ : ℝ) : ℂ) * Complex.I) * (γ' s * Q' s)) →
        ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ s : ℂ, ΛQd (1 - s) = ε * ((Nf : ℂ) ^ (s - 1 / 2)) * ΛQ s) := by sorry
