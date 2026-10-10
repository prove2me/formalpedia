-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_theorem_1_5
-- name    : NeuroMV.WellPosed.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:09.1135+00:00
-- url     : https://prove2.me/theorems/312b7946-34f4-4a21-900f-cd4154860c59
-- title:
--   Theorem 1.5, p. 7 — (6) has a unique strong solution in L∞([−τ,T]; L²(Ω×Γ, ℙ⊗𝓡)), measurable in (r, ω′), for ℙ′-a.e. ω′
-- statement:
--   Consider the spatially structured McKean–Vlasov delay equation with jumps
--
--   $$dX^r_t = f(t,r,X^r_{t-},\omega')dt + g(t,r,X^r_{t-},\omega')dW_t + \int_U h(t,r,X^r_{t-},\omega',\xi)\tilde N(dt,d\xi) + \sum_{\alpha=1}^P\int_{\Gamma_\alpha}\tilde{\mathbb E}\big[\theta(t,r,r',X^r_{t-},\tilde X^{r'}_{(t-\tau)^-:t^-},\omega')\big]\mathcal R(dr')dt$$
--   $$+ \sum_{\alpha=1}^P\int_{\Gamma_\alpha}\tilde{\mathbb E}\big[\beta(\cdots)\big]\mathcal R(dr')dB^\alpha_t + \sum_{\alpha=1}^P\int_{\Gamma_\alpha}\int_U\tilde{\mathbb E}\big[\eta(\cdots,\xi)\big]\mathcal R(dr')\tilde N^\alpha(dt,d\xi),\qquad X^r_t = \hat z^\zeta_t,\ r\in\Gamma_\zeta,\ t\in[-\tau,0], \tag{6}$$
--
--   where $\tilde X$ is a copy of $X$ on another probability space and $\tilde{\mathbb E}$ its expectation, under the standing assumptions of §1 and Hypothesis 1.1 (H1)–(H5), with disorder space $(\Omega',\mathcal F',\mathbb P')$.
--
--   **Theorem 1.5.** For any $T > 0$ there is $X^r_t(\omega;\omega')$, measurable in $(r,\omega',\omega)$ for each $t\in[-\tau,T]$, such that for $\mathbb P'$-almost every $\omega'$:
--   1. $X(\omega')$ is a strong solution of (6) on $[-\tau,T]$;
--   2. $X(\omega') \in L^\infty([-\tau,T],dt;L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R;\mathbb R^d))$;
--   3. it is unique in that class: every strong solution $Y$ of (6) on $[-\tau,T]$ at $\omega'$ in the same class satisfies $\int_\Gamma\mathbb E|X^r_t(\omega') - Y^r_t|^2\,\mathcal R(dr) = 0$ for every $t\in[-\tau,T]$.
--
--   This is the first main result of the paper: the infinite-population limit of the neuronal network (1) is well defined, which is what the propagation-of-chaos result Theorem 1.8 converges to.
--
--   **Formalization Note.** The solution property (the integral form of (6)) is required at **every** $r\in\Gamma$, as (6) is posed; the existence proof in §2 concludes "for $\mathcal R\times\mathbb P'$-almost all $(r,\omega')$" (p. 16), and on the remaining $\mathcal R$-null set of positions (6) is an ordinary delay SDE whose mean-field coefficients are already determined, so Theorem A.2 solves it — a step the paper does not write. (H6) is omitted: it involves the network data $\mathcal A_N$, $\mathcal S_{\mathcal A_N,\alpha}$ of (1), which do not occur in (6), and the proof never uses it. The class is a bound $\sup_{t\in[-\tau,T]}\int_\Gamma\mathbb E|X^r_t|^2\mathcal R(dr) < \infty$ for every $t$ rather than for a.e. $t$ (by Lemma 1.4 these agree for solutions). Uniqueness is in $L^2(\Omega\times\Gamma)$ at each time, as the proof on p. 17 gives it. Expectations are lower integrals in $[0,\infty]$.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Theorem 1.5, p. 7, with (6), p. 5, and Hypothesis 1.1, pp. 3–4

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem theorem_1_5
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (prob' : Measure Ω') [IsProbabilityMeasure prob'] (T : ℝ) (hT : 0 < T) :
    ∃ X : Ω' → Pos k → ℝ → Ω → SDEState d,
      (∀ t ∈ Set.Icc (-τ) T, Measurable (fun p : Pos k × Ω' × Ω => X p.2.1 p.1 t p.2.2)) ∧
      ∀ᵐ ω' ∂prob',
        IsStrongSol6 S C ν Nz τ ω' T (X ω') ∧ InClass S Nz.prob τ T (X ω') ∧
        ∀ Y : Pos k → ℝ → Ω → SDEState d,
          IsStrongSol6 S C ν Nz τ ω' T Y → InClass S Nz.prob τ T Y →
            ∀ t ∈ Set.Icc (-τ) T, ∫⁻ r, ∫⁻ ω, ‖X ω' r t ω - Y r t ω‖ₑ ^ 2 ∂Nz.prob ∂S.R = 0 := by sorry

end NeuroMV.WellPosed
