-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_lemma_2_slow
-- name    : NetTraffic.PoissonStable.lemma_2_slow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:27.560215+00:00
-- url     : https://prove2.me/theorems/35165fdf-570f-4912-99dd-5e7ea3555b0f
-- title:
--   Lemma 2 (3.4), slow part, p. 31 — under Condition 1, λT² F̄_on(T)/b(λT) → 0
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$.
--
--   If Condition 1 holds, then
--   $$\lim_{T\to\infty}\frac{\lambda T^2\,\bar F_{\mathrm{on}}(T)}{b(\lambda T)}=0 .$$
--
--   This is the estimate that makes every remainder term of order $\lambda T^2\bar F_{\mathrm{on}}(T)$ negligible against the stable normalisation $b(\lambda T)$.
--
--   **Formalization Note** Only the Condition 1 half of Lemma 2 is stated here; the Condition 2 half belongs to the companion mission on fast growth.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 31, Lemma 2 (3.4), Condition 1 part

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_2_slow
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam) :
    Tendsto (fun T => lam T * T ^ 2 * Fbar Fon T / b Fon (lam T * T)) atTop (𝓝 0) := by sorry

end NetTraffic.PoissonStable
