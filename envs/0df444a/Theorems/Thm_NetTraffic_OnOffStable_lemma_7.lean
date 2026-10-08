-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_7
-- name    : NetTraffic.OnOffStable.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:17.137177+00:00
-- url     : https://prove2.me/theorems/41e3934f-fab5-4f84-a4e3-6120ea225e06
-- title:
--   Lemma 7, p. 48 — M P(−S⁽¹⁾_{[μ_T]} > x b(MT)) → 0
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2), let $M=M(T)$ satisfy Slow Growth Condition 1, and let
--   $$S^{(1)}_n=r_{\mathrm{on}}\sum_{k=1}^n(X_k-\mu_{\mathrm{on}}),\qquad r_{\mathrm{on}}=\mu_{\mathrm{off}}/\mu .$$
--   Then for every $x>0$,
--   $$M\,P\bigl(-S^{(1)}_{[\mu_T]}>x\,b(MT)\bigr)=o(1)\qquad(T\to\infty),$$
--   where $\mu_T=T/\mu$ and $[\cdot]$ is the integer part.
--
--   The left tail of the centred ON-period sums is negligible at the scale $b(MT)$; this is used in Lemma 9 and in condition (B) of Lemma 10.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 48, Lemma 7

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_7
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun T => (M T : ℝ) *
      P.real {ω | x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < -s.S1 Fon Foff ⌊muT Fon Foff T⌋₊ ω})
      atTop (𝓝 0) := by sorry

end NetTraffic.OnOffStable
