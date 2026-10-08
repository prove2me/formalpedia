-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_2_14
-- name    : NetTraffic.PoissonFBM.eq_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:53.519746+00:00
-- url     : https://prove2.me/theorems/8179c1a6-ef2a-4d28-a4e3-670c4d836447
-- title:
--   (2.14), p. 29 — Cov(N(t), N(t+h)) = λ∫_h^∞ F̄_on(v) dv ∼ (const) h F̄_on(h)
-- statement:
--   Consider the infinite source Poisson model with rate $\lambda>0$ and length law $F_{\mathrm{on}}$ satisfying (2.8), $1<\alpha<2$. For every $t\in\mathbb R$ and every $h\ge0$,
--   $$\mathrm{Cov}\big(N(t),N(t+h)\big)=\lambda\int_h^\infty\bar F_{\mathrm{on}}(v)\,dv ,$$
--   and there is a constant $c>0$ with
--   $$\lim_{h\to\infty}\frac{\int_h^\infty\bar F_{\mathrm{on}}(v)\,dv}{h\,\bar F_{\mathrm{on}}(h)}=c .$$
--
--   The identity says that the input rate is long-range dependent: its covariance decays like $h^{-(\alpha-1)}L(h)$, which is not integrable. It drives Lemma 1 and the variance of the cumulative input.
--
--   **Formalization Note** The page writes "$\sim(\mathrm{const})\,h\bar F_{\mathrm{on}}(h)$" without naming the constant; it is stated as the existence of a positive limit of the ratio (the constant $\lambda$ is dropped from both sides).
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 29, (2.14)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (2.14), p. 29: in the infinite source Poisson model with rate `λ > 0`,
`Cov(N(t), N(t + h)) = λ ∫_h^∞ F̄_on(v) dv` for all `t` and `h ≥ 0`, and
`∫_h^∞ F̄_on(v) dv ∼ (const) h F̄_on(h)` as `h → ∞`. -/
theorem eq_2_14
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ) (hlam : 0 < lam) (Γ X : ℤ → Ω → ℝ) (hmodel : NetTraffic.PoissonStable.IsPoissonModel P lam Fon Γ X) :
    (∀ t h : ℝ, 0 ≤ h →
      cov[fun ω => (NetTraffic.PoissonStable.N Γ X t ω : ℝ), fun ω => (NetTraffic.PoissonStable.N Γ X (t + h) ω : ℝ); P] =
        lam * ∫ v in Set.Ioi h, NetTraffic.PoissonStable.Fbar Fon v) ∧
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun h => (∫ v in Set.Ioi h, NetTraffic.PoissonStable.Fbar Fon v) / (h * NetTraffic.PoissonStable.Fbar Fon h)) atTop (𝓝 c) := by sorry

end NetTraffic.PoissonFBM
