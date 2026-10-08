-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_remark_4_eq_11
-- name    : ModelRiskOT.WorstProb.remark_4_eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:05:24.778579+00:00
-- url     : https://prove2.me/theorems/a9f60520-47c9-485f-bffc-cc23d6aedae8
-- title:
--   Remark 4, (11) for $f = 1_A$ — $\varepsilon$-optimal plans nearly satisfy complementary slackness
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $\mu$ a probability measure on $S$, $\delta > 0$, $A \subseteq S$ nonempty and closed, and $I = \sup\{\pi(S \times A) : \pi \in \Phi_{\mu,\delta}\}$. Let $\lambda^* \ge 0$ be such that $(\lambda^*, \varphi_{\lambda^*})$ is dual optimal, where $\varphi_{\lambda^*}(x) = (1 - \lambda^* c(x,A))^+$; that is,
--   $$I = \lambda^*\delta + E_\mu\big[(1 - \lambda^* c(X,A))^+\big].$$
--   Let $\varepsilon > 0$ and let $\pi_\varepsilon \in \Phi_{\mu,\delta}$ satisfy $\pi_\varepsilon(S \times A) \ge I - \varepsilon$. Then
--   $$\int \Big(\varphi_{\lambda^*}(x) - \big(1_A(y) - \lambda^* c(x,y)\big)\Big)\,d\pi_\varepsilon(x,y) \le \varepsilon,$$
--   and, if $\lambda^* > 0$,
--   $$\Big(\delta - \frac{\varepsilon}{\lambda^*}\Big)^+ \le \int c\,d\pi_\varepsilon \le \delta .$$
--
--   The two bounds say that an $\varepsilon$-optimal transport plan almost moves mass only to maximizers of $1_A(y) - \lambda^* c(x,y)$ and almost exhausts the budget; they are the quantitative form of the complementary slackness conditions, and Lemma 4 and Lemma 2 are built on them.
--
--   **Formalization Note** The page prints the first integrand as $\varphi_{\lambda^*}(x) - f(y) - \lambda^* c(x,y)$; the statement uses the integrand of (10), $\varphi_{\lambda^*}(x) - (f(y) - \lambda^* c(x,y))$, which is nonnegative. The second bound is stated only for $\lambda^* > 0$, where $\varepsilon/\lambda^*$ is defined (the only case the paper uses). Dual optimality is stated as the equality above, which is $I = J(\lambda^*, \varphi_{\lambda^*})$ after the identity $\sup_y\{1_A(y) - \lambda c(x,y)\} = (1 - \lambda c(x,A))^+$. The condition $\pi_\varepsilon(S\times A) \ge I - \varepsilon$ is written $I \le \pi_\varepsilon(S \times A) + \varepsilon$ in $[0,\infty]$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 8, Remark 4, Eq. (11), for f = 1_A

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_WorstCaseProb

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- Remark 4, (11), p. 8, for `f = 1_A`. Let `(λ*, φ_{λ*})` be dual optimal, where by §2.4
`φ_{λ*}(x) = (1 − λ* c(x, A))⁺`; i.e. `I = λ*δ + E_μ[(1 − λ* c(X, A))⁺]` with
`I = sup {π(S × A) : π ∈ Φ_{μ,δ}}`. Then for `ε > 0` and every `π_ε ∈ Φ_{μ,δ}` with
`π_ε(S × A) ≥ I − ε`:
`∫ (φ_{λ*}(x) − (1_A(y) − λ* c(x, y))) dπ_ε ≤ ε`, and, when `λ* > 0`,
`(δ − ε/λ*)⁺ ≤ ∫ c dπ_ε ≤ δ`.
The integrand is the corrected one of (10) (the page prints `φ_{λ*}(x) − f(y) − λ* c(x, y)`). -/
theorem remark_4_eq_11 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hdual : worstProbCoupling c μ δ A = obj13 c μ δ A lamStar)
    (ε : ℝ) (hε : 0 < ε) (π : Measure (S × S)) (hπ : π ∈ Phi c μ δ)
    (hπε : worstProbCoupling c μ δ A ≤ π (Set.univ ×ˢ A) + ENNReal.ofReal ε) :
    ∫⁻ p, ENNReal.ofReal (max (1 - lamStar * costToSet c A p.1) 0 -
        (A.indicator (fun _ => (1 : ℝ)) p.2 - lamStar * c p.1 p.2)) ∂π ≤ ENNReal.ofReal ε ∧
    (0 < lamStar →
      ENNReal.ofReal (δ - ε / lamStar) ≤ ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π ∧
      ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π ≤ ENNReal.ofReal δ) := by sorry

end ModelRiskOT.WorstProb
