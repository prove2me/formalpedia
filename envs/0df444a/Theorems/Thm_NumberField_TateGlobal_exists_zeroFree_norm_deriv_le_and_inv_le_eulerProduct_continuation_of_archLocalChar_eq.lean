-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
-- name    : NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/ecb98452-c4d2-5b41-b576-000133eadaa1
-- title:
--   Uniform zero-free region and L'/L bounds for Hecke L-functions
-- statement:
--   Let $K$ be a number field, $S$ a finite set of nonzero primes of $\mathcal O_K$, and $\rho$ a family assigning to every nonzero prime $v$ a homomorphism $(K_v)^\times \to \mathbb C^\times$. The assertion is that there exist reals $c_0, C > 0$ and a natural number $A$ such that for every homomorphism $\chi : (\mathbb A_K)^\times \to \mathbb C^\times$ which is continuous as a $\mathbb C$-valued function, unitary ($\|\chi(x)\| = 1$ for all $x$), trivial on the image of $K^\times$, unramified at each $v \notin S$ in the sense that the local component $\mathrm{localChar}\,\chi\,v$ (the restriction of $\chi$ to ideles supported at $v$) is trivial on every $u$ with $u, u^{-1}$ integral, and with $\mathrm{localChar}\,\chi\,v = \rho_v$ on such $u$ for $v \in S$, the following holds for the Euler product $P(w) = \prod'_v (1 - c_v N(v)^{-w})^{-1}$, where $N(v) = \mathrm{absNorm}(v)$ and $c_v = \chi(\varpi_v)$ (the idele which is a uniformiser at $v$ and $1$ elsewhere) when $\chi$ is unramified at $v$, and $c_v = 0$ otherwise. (i) Let $\tau : \mathrm{InfinitePlace}\,K \to \mathbb R$ and $m : \mathrm{InfinitePlace}\,K \to \mathbb Z$ be such that, at each infinite place $v$ and each $x \in (K_v)^\times$: if the image of $x$ under the embedding of $K_v$ into $\mathbb C$ is a positive real then $\chi$ evaluated on the idele equal to $x$ at $v$ and $1$ elsewhere equals $\mathrm{ideleNorm}$ of that idele raised to the power $\tau_v i$, and if that image has absolute value $1$ then the same value equals the image raised to the power $m_v$. Assume $\chi \neq \mathrm{normPowChar}\,K\,\tau_0$ (the character $x \mapsto \mathrm{ideleNorm}(x)^{i\tau_0}$) for every real $\tau_0$, and let $L$ be entire with $L = P$ on $\mathrm{Re}\,w > 1$. Then for all reals $t, \sigma$, putting $T = 2 + |t| + \sum_v (|\tau_v| + |m_v|)$, if $1 - c_0/\log T \le \sigma \le 2$ then $L(\sigma + it) \neq 0$, $\|L'(\sigma + it)\| \le C T^A \|L(\sigma + it)\|$ and $1 \le C T^A \|L(\sigma + it)\|$. (ii) If $\chi = \mathrm{normPowChar}\,K\,\tau_0$ for some real $\tau_0$ and $Q$ is entire with $Q(w) = (w - (1 - i\tau_0))P(w)$ on $\mathrm{Re}\,w > 1$, the same three conclusions hold for $Q$ at $\sigma + it$ with $T = 2 + |t + \tau_0|$.
--
--   This is the de la Vallée Poussin zero-free region for Hecke $L$-functions over a number field, together with the attendant bounds for $L'/L$ and for $1/L$ inside the region, the constants being uniform in the character: the finite part of the conductor is pinned down by $S$ and $\rho$, while the archimedean parameters $\tau_v$ and weights $m_v$ (and the height $t$) enter only through $T$; in the norm-power case the factor $w - (1 - i\tau_0)$ removes the pole. It feeds the analytic estimates used for adelic automorphic forms, being cited in the construction of entire continuations of Euler products attached to induced sections and in the bound for the derivative of the Weyl intertwining integral on the critical axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq.lean

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

theorem NumberField.TateGlobal.exists_zeroFree_norm_deriv_le_and_inv_le_eulerProduct_continuation_of_archLocalChar_eq
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ (c₀ C : ℝ) (A : ℕ), 0 < c₀ ∧ 0 < C ∧
    ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
      (_hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ) (_hχF : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ)
      (_hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v)
      (_hram : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K → localChar χ v u = ρ v u),
    let P : ℂ → ℂ := fun w => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹
    (∀ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
        (_hτ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (((ideleNorm K (archUnitHom v x)) : ℝ) : ℂ) ^ (((τ v : ℝ) : ℂ) * Complex.I))
        (_hm : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
          ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
          ((archLocalChar χ v x : ℂˣ) : ℂ) =
            (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v))
        (_hχ1 : ∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀)
        (L : ℂ → ℂ) (_hL : Differentiable ℂ L) (_hLP : ∀ w : ℂ, 1 < w.re → L w = P w)
        (t σ : ℝ),
        let T : ℝ := 2 + |t| + ∑ v : InfinitePlace K, (|τ v| + (|m v| : ℝ))
        1 - c₀ / Real.log T ≤ σ → σ ≤ 2 →
          L ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * T ^ A * ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          1 ≤ C * T ^ A * ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ∧
    (∀ (τ₀ : ℝ) (_hχ0 : χ = normPowChar K τ₀)
        (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
        (_hQP : ∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * P w)
        (t σ : ℝ),
        let T : ℝ := 2 + |t + τ₀|
        1 - c₀ / Real.log T ≤ σ → σ ≤ 2 →
          Q ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
          ‖deriv Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * T ^ A * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
          1 ≤ C * T ^ A * ‖Q ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by sorry
