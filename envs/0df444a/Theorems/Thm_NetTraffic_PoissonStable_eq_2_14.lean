-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_2_14
-- name    : NetTraffic.PoissonStable.eq_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:03.489424+00:00
-- url     : https://prove2.me/theorems/4b1f1431-3695-4fd5-b491-570ca4893953
-- title:
--   (2.14), p. 29 — Cov(N(t), N(t+h)) = λ∫_h^∞ F̄_on(v) dv ∼ (const) h F̄_on(h)
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$.
--
--   Consider one infinite source Poisson model with rate $\lambda>0$ (points $\Gamma_k$, iid lengths $X_k\sim F_{\mathrm{on}}$) and its number of active sources $N(t)$. Then for every $t\in\mathbb R$ and $h\ge0$
--   $$\mathrm{Cov}(N(t),N(t+h))=\lambda\int_h^\infty\bar F_{\mathrm{on}}(v)\,dv,$$
--   and there is a constant $c>0$ such that, for every $t$,
--   $$\frac{\mathrm{Cov}(N(t),N(t+h))}{h\,\bar F_{\mathrm{on}}(h)}\to c\qquad(h\to\infty).$$
--
--   The covariance identity exhibits long-range dependence in the input rate: the covariance decays like $h^{-(\alpha-1)}L(h)$, which is not integrable.
--
--   **Formalization Note** The "(const)" of the page is an existentially quantified $c>0$ chosen before $t$; the page's second equality $=(\mathrm{const})h^{-(\alpha-1)}L(h)$ is the definition of $L$ and is not restated.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 29, (2.14)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_2_14
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {lam : ℝ} (hlam : 0 < lam) {Γ X : ℤ → Ω → ℝ} (hmodel : IsPoissonModel P lam Fon Γ X) :
    (∀ t h : ℝ, 0 ≤ h →
      cov[fun ω => (N Γ X t ω : ℝ), fun ω => (N Γ X (t + h) ω : ℝ); P] =
        lam * ∫ v in Set.Ioi h, Fbar Fon v) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      Tendsto (fun h => cov[fun ω => (N Γ X t ω : ℝ), fun ω => (N Γ X (t + h) ω : ℝ); P] /
        (h * Fbar Fon h)) atTop (𝓝 c) := by sorry

end NetTraffic.PoissonStable
