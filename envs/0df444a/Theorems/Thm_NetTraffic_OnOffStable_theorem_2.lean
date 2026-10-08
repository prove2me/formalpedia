-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_theorem_2
-- name    : NetTraffic.OnOffStable.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:36.629696+00:00
-- url     : https://prove2.me/theorems/70c3b083-93c6-4091-8bdd-c3168d87c7d1
-- title:
--   Theorem 2, p. 40 — under slow growth, (A(T·) − TMμ⁻¹μ_on(·))/b(MT) →fidi c X_{α,σ,1}
-- statement:
--   Consider $M=M(T)$ independent stationary ON/OFF sources whose ON- and OFF-period laws satisfy (2.1)–(2.2): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L_{\mathrm{on}}(x)$, $\bar F_{\mathrm{off}}(x)=x^{-\alpha_{\mathrm{off}}}L_{\mathrm{off}}(x)$, $1<\alpha<\alpha_{\mathrm{off}}<2$. Let $A(t)=\int_0^tN(s)\,ds$ be the cumulative input of the superposition, $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$, $b$ the quantile function (2.9) of $F_{\mathrm{on}}$, and
--   $$c=\frac{\mu_{\mathrm{off}}}{\mu^{1+1/\alpha}},\qquad \sigma=C_\alpha^{-1/\alpha},\qquad C_\alpha=\frac{1-\alpha}{\Gamma(2-\alpha)\cos(\pi\alpha/2)} .$$
--   If Slow Growth Condition 1 holds ($M(T)$ non-decreasing, $M(T)\to\infty$, $b(MT)/T\to0$), then
--   $$\frac{A(T\cdot)-TM\mu^{-1}\mu_{\mathrm{on}}(\cdot)}{b(MT)}\xrightarrow{\ fidi\ }c\,X_{\alpha,\sigma,1}(\cdot),$$
--   where $X_{\alpha,\sigma,1}$ is the α-stable Lévy motion with $X(t)\sim S_\alpha(\sigma t^{1/\alpha},1,0)$: for all $0\le t_1\le\dots\le t_k$, the joint law of the normalised input at $t_1,\dots,t_k$ converges weakly to that of $(cX_{\alpha,\sigma,1}(t_1),\dots,cX_{\alpha,\sigma,1}(t_k))$.
--
--   This is the paper's main result for the ON/OFF model: when the number of sources grows slowly relative to the time scale, the centred cumulative input is approximated by a totally skewed α-stable Lévy motion, not by fractional Brownian motion (compare Theorem 4).
--
--   **Formalization Note.** Mathlib has no stable laws, so the statement asserts that for each $k$ and each sorted $t$ with $t_1\ge0$ there is a probability measure $\nu$ on $\mathbb R^k$ (`EuclideanSpace ℝ (Fin k)`) whose characteristic function at $\theta$ is the joint characteristic function of $(X_{\alpha,\sigma,1}(t_1),\dots,X_{\alpha,\sigma,1}(t_k))$ at $c\theta$, i.e. $\nu$ is the law of $c\,(X(t_1),\dots,X(t_k))$, and that the laws of the normalised input vectors converge weakly to $\nu$. Sorting the times loses nothing. Each time scale $T$ has its own probability space carrying $M(T)$ independent sources. The constant $c$ multiplies the process, as on the page; equivalently $cX_{\alpha,\sigma,1}$ has the law of $X_{\alpha,c\sigma,1}$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 40, (5.1) and Theorem 2

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem theorem_2
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hsrc : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∀ (k : ℕ) (t : Fin k → ℝ), Monotone t → (∀ j, 0 ≤ t j) →
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
        (∀ θ : EuclideanSpace ℝ (Fin k), charFun (ν : Measure (EuclideanSpace ℝ (Fin k))) θ =
          NetTraffic.PoissonStable.stableLevyFidiCharFun α (NetTraffic.PoissonStable.sigmaConst α) 1 t (cConst Fon Foff α • θ)) ∧
        NetTraffic.PoissonStable.TendstoInLaw P (fun T ω =>
          (WithLp.toLp 2 (fun j => Gnorm Fon Foff M (src T) T (t j) ω) :
            EuclideanSpace ℝ (Fin k))) ν := by sorry

end NetTraffic.OnOffStable
