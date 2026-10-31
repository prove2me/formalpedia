-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_eq_2_57_2_58
-- name    : KallMayerSLP.SimpleRecourse.eq_2_57_2_58
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:05.22616+00:00
-- url     : https://prove2.me/theorems/9b601361-988a-4b66-9286-a449bac4bb70
-- title:
--   (2.57)–(2.58) — the expected MSRT function via shifted laws, and the mixture distribution function $G$
-- statement:
--   Let the constants satisfy Definition 2.4, let $\tilde\xi$ have law $\mathbb P_{\tilde\xi}$, distribution function $F_{\tilde\xi}$ and finite mean, and let $\Psi$ be the expected MSRT function. Then
--
--   1. $\Psi(z)=\mathbb E_{\tilde\xi}[\psi(z,\tilde\xi)]$;
--   2. $\xi\mapsto F_{\tilde\xi}(\xi+u_k)$ is the distribution function of $\tilde\xi-u_k$, and $\xi\mapsto F_{\tilde\xi}(\xi-l_k)$ that of $\tilde\xi+l_k$;
--   3. for every $z$
--   $$
--   \Psi(z)+\gamma=\sum_{k=0}^{K-1}\alpha_k\int_{-\infty}^\infty(\xi-z)^+\,dF_{\tilde\xi}(\xi+u_k)+\sum_{k=0}^{K-1}\beta_k\int_{-\infty}^\infty(\xi-z)^-\,dF_{\tilde\xi}(\xi-l_k); \tag{2.57}
--   $$
--   4. $H(\xi)=\sum_k\alpha_kF_{\tilde\xi}(\xi+u_k)+\sum_k\beta_kF_{\tilde\xi}(\xi-l_k)$ is monotonically increasing and right-continuous, $H\ge0$, $\lim_{\xi\to-\infty}H(\xi)=0$ and $\lim_{\xi\to\infty}H(\xi)=W:=\sum_k(\alpha_k+\beta_k)>0$;
--   5. $G=H/W$ of (2.58) is a distribution function: monotone, right-continuous, with limits $0$ at $-\infty$ and $1$ at $+\infty$.
--
--   (2.57) shows a formal similarity with an expected SRT function, and (2.58) supplies the distribution that makes it exact (Theorem 2.8).
--
--   **Formalization Note** $dF_{\tilde\xi}(\xi+u_k)$ is integration against the law of $\tilde\xi-u_k$, and $dF_{\tilde\xi}(\xi-l_k)$ against the law of $\tilde\xi+l_k$; item 2 identifies their distribution functions.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: 𝔼_ξ̃[ξ̃] provided to exist (Definition 2.3) → Integrable (fun ξ => ξ) P; reason: existence of a finite mean is integrability of the identity under the law
--   - encoding: ∫ … dF_ξ̃(ξ + u_k) and ∫ … dF_ξ̃(ξ − l_k) → integrals against P.map (· − u k) and P.map (· + l k), with their cdfs proved equal to F_ξ̃(· + u_k), F_ξ̃(· − l_k); reason: a Stieltjes integral against a distribution function is the integral against the probability measure it determines
--   - encoding: G is a new distribution function → Monotone G, right-continuous, limits 0 at −∞ and 1 at +∞; reason: the defining properties of a distribution function on ℝ
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.57)–(2.58), pp.239–240 (PDF 248–249)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsMSRTData
import Definitions.Def_KallMayerSLP_SimpleRecourse_msrt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedMSRT
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureH
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureCdf

open MeasureTheory ProbabilityTheory Filter Topology

namespace KallMayerSLP.SimpleRecourse

/-- **(2.57)–(2.58): the expected MSRT function as a sum of shifted SRT integrals, and the mixture
distribution function `G`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, pp.239–240 (PDF 248–249).
For the expected MSRT function `Ψ(z) = 𝔼_ξ̃[ψ(z, ξ̃)]` of Definition 2.4,
`Ψ(z) + γ = Σ_{k=0}^{K−1} α_k ∫ (ξ − z)⁺ dF_ξ̃(ξ + u_k) + Σ_{k=0}^{K−1} β_k ∫ (ξ − z)⁻ dF_ξ̃(ξ − l_k)` (2.57).
`H(ξ) = Σ_k α_k F_ξ̃(ξ + u_k) + Σ_k β_k F_ξ̃(ξ − l_k)` is monotonically increasing,
right-continuous, and satisfies `H(ξ) ≥ 0 ∀ξ`, `lim_{ξ→−∞} H(ξ) = 0`,
`lim_{ξ→∞} H(ξ) = Σ_k (α_k + β_k) > 0`, so that `G(ξ) := H(ξ)/W`, `W := Σ_k (α_k + β_k)`, is a
new distribution function (2.58).

**Formalization Note.** `P` is the distribution of `ξ̃` and `F_ξ̃ = cdf P`. `dF_ξ̃(ξ + u_k)` is
integration against the law of `ξ̃ − u_k`, `P.map (· − u k)`, whose distribution function is
`ξ ↦ F_ξ̃(ξ + u_k)`; `dF_ξ̃(ξ − l_k)` against the law of `ξ̃ + l_k`, `P.map (· + l k)`, with
distribution function `ξ ↦ F_ξ̃(ξ − l_k)`; both identities are stated. "Distribution function" is
spelled out: monotone, right-continuous, limits `0` at `−∞` and `1` at `+∞`. The first conjunct is
the defining identity `Ψ(z) = 𝔼_ξ̃[ψ(z, ξ̃)]` of Definition 2.4. -/
theorem eq_2_57_2_58 {K : ℕ} (α β u l : Fin K → ℝ) (hd : IsMSRTData K α β u l) (γ : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable (fun ξ => ξ) P) :
    (∀ z : ℝ, expectedMSRT α β u l γ P z = ∫ ξ, msrt α β u l γ z ξ ∂P) ∧
    (∀ k : Fin K, ⇑(cdf (P.map (fun ξ => ξ - u k))) = fun ξ => cdf P (ξ + u k)) ∧
    (∀ k : Fin K, ⇑(cdf (P.map (fun ξ => ξ + l k))) = fun ξ => cdf P (ξ - l k)) ∧
    (∀ z : ℝ, expectedMSRT α β u l γ P z + γ =
      ∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) +
        ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k))) ∧
    Monotone (mixtureH α β u l P) ∧
    (∀ x : ℝ, ContinuousWithinAt (mixtureH α β u l P) (Set.Ici x) x) ∧
    (∀ ξ : ℝ, 0 ≤ mixtureH α β u l P ξ) ∧
    Tendsto (mixtureH α β u l P) atBot (𝓝 0) ∧
    Tendsto (mixtureH α β u l P) atTop (𝓝 (∑ k, (α k + β k))) ∧
    0 < ∑ k, (α k + β k) ∧
    Monotone (mixtureCdf α β u l P) ∧
    (∀ x : ℝ, ContinuousWithinAt (mixtureCdf α β u l P) (Set.Ici x) x) ∧
    Tendsto (mixtureCdf α β u l P) atBot (𝓝 0) ∧
    Tendsto (mixtureCdf α β u l P) atTop (𝓝 1) := by sorry

end KallMayerSLP.SimpleRecourse
