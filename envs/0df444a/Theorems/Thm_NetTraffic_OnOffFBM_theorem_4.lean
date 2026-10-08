-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_theorem_4
-- name    : NetTraffic.OnOffFBM.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:46.448783+00:00
-- url     : https://prove2.me/theorems/f05ae606-132b-422d-aa16-7554eea5afef
-- title:
--   Theorem 4 (7.2), p. 62 — under fast growth, (A(T·) − TMμ^{−1}μ_on(·))/d_T →d σ₀ B_H(·) in ℂ[0,∞), H = (3 − α)/2
-- statement:
--   Consider $M=M(T)$ independent stationary ON/OFF sources whose ON- and OFF-period laws satisfy (2.1)–(2.2), $1<\alpha=\alpha_{\mathrm{on}}<\alpha_{\mathrm{off}}<2$, with $M$ integer valued, non-decreasing and $M(T)\to\infty$, and let $A(t)=\int_0^t\sum_{m=1}^MW^{(m)}_s\,ds$ be the cumulative input. If Fast Growth Condition 2, $b(MT)/T\to\infty$, holds, then
--   $$\frac{A(T\cdot)-TM\mu^{-1}\mu_{\mathrm{on}}(\cdot)}{d_T}\ \xrightarrow{d}\ \sigma_0B_H(\cdot)\qquad(T\to\infty)$$
--   weakly in $\mathbb C[0,\infty)$, where $d_T=[T^{3-\alpha}L_{\mathrm{on}}(T)M]^{1/2}$, $\sigma_0^2=\dfrac{2\mu_{\mathrm{off}}^2\Gamma(2-\alpha)/(\alpha-1)}{\mu^3\Gamma(4-\alpha)}$, $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$, and $B_H$ is standard fractional Brownian motion with $H=(3-\alpha)/2$.
--
--   This is the fast-growth half of the paper's dichotomy for the ON/OFF model: when the number of sources grows fast relative to the time scale, the cumulative input of many heavy-tailed sources is approximately a Gaussian long-range-dependent process, as opposed to the stable Lévy motion of the slow-growth regime (Theorem 2).
--
--   **Formalization Note** Weak convergence is stated in coupling form (Skorokhod representation): for every sequence $T_n\to\infty$ there are a probability space, processes $Y_n$ with continuous paths whose laws on $\mathbb R^{[0,\infty)}$ (all finite-dimensional distributions) are those of the normalised input at $T_n$, and a standard fractional Brownian motion $Y'$, such that almost surely $Y_n\to\sigma_0Y'$ uniformly on every $[0,K]$. Since the prelimit and the limit have continuous paths and $\mathbb C[0,\infty)$ is Polish, this is equivalent to weak convergence in $\mathbb C[0,\infty)$. Each model $T$ has its own probability space and the statement holds for every family of models with the stated laws.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 62, Theorem 4, (7.2)

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- Theorem 4, p. 62: under (2.1)–(2.2), `M` non-decreasing with `M → ∞`, and Condition 2,
`(A(T·) - TMμ^{-1}μ_on(·))/d_T →d σ_0 B_H(·)` in `ℂ[0, ∞)`, where `B_H` is a standard fractional
Brownian motion with `H = (3 - α)/2`. Weak convergence is stated in coupling form: along every
sequence `T_n → ∞` there are, on one probability space, continuous copies `Y_n` of the laws of
the normalised processes at `T_n` and a standard FBM `Y'` with `Y_n → σ_0 Y'` uniformly on
compacts almost surely. -/
theorem theorem_4
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∀ Tn : ℕ → ℝ, Tendsto Tn atTop atTop →
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → ℝ≥0 → Ω₀ → ℝ)
        (Y' : ℝ≥0 → Ω₀ → ℝ),
        IsProbabilityMeasure Q ∧
        (∀ n, Measurable (fun ω (t : ℝ≥0) => Y n t ω)) ∧
        (∀ n, ∀ᵐ ω ∂Q, Continuous (fun t => Y n t ω)) ∧
        (∀ n, Q.map (fun ω (t : ℝ≥0) => Y n t ω) =
          (P (Tn n)).map (fun ω (t : ℝ≥0) => Gnorm Fon Foff α M (src (Tn n)) (Tn n) t ω)) ∧
        IsStdFBM (hurst α) Y' Q ∧
        ∀ᵐ ω ∂Q, UocTendsto (fun n t => Y n t ω) (fun t => sigma0 Fon Foff α * Y' t ω) := by sorry

end NetTraffic.OnOffFBM
