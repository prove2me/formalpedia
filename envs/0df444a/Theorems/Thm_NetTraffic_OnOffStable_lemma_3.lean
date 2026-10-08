-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_3
-- name    : NetTraffic.OnOffStable.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:41.882716+00:00
-- url     : https://prove2.me/theorems/017cc982-c4bc-4049-aba6-efad558ea7aa
-- title:
--   Lemma 3, p. 41 — [b(MT)]⁻¹(A₁ − EA₁) → 0 in probability
-- statement:
--   Consider $M=M(T)$ independent stationary ON/OFF sources with ON-period law $F_{\mathrm{on}}$ and OFF-period law $F_{\mathrm{off}}$ satisfying (2.1)–(2.2) ($1<\alpha<\alpha_{\mathrm{off}}<2$), and suppose Slow Growth Condition 1, $b(MT)/T\to0$, holds. Let
--   $$A_1=\sum_{m=1}^M B^{(m)}\min\bigl(T,(X^{(0)}_{\mathrm{on}})^{(m)}\bigr)$$
--   be the contribution of the initial ON-periods to the cumulative input $A(T)$. Then, as $T\to\infty$,
--   $$[b(MT)]^{-1}(A_1-EA_1)\xrightarrow{P}0 .$$
--
--   This is the first of the two negligibility results of §5.3: the initial ON-periods do not contribute to the stable limit of Theorem 2.
--
--   **Formalization Note.** For each $T$ the model lives on its own probability space $(\Omega_T,P_T)$; convergence in probability means $P_T(|Y_T|>\eta)\to0$ for every $\eta>0$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 41, Lemma 3

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_3
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hsrc : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    NetTraffic.PoissonStable.TendstoInProbZero P (fun T ω =>
      (A1 (M T) (src T) T ω - (P T)[A1 (M T) (src T) T]) / NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)) := by sorry

end NetTraffic.OnOffStable
