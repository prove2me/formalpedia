-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_5
-- name    : NetTraffic.OnOffStable.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:48.7476+00:00
-- url     : https://prove2.me/theorems/08e90602-cb79-495b-a4c1-187f6fcacb85
-- title:
--   Lemma 5, p. 43 — M[b(MT)]⁻¹ E X_{ξ_T} 1[X_{ξ_T} > δb(MT)] 1[ξ_T ≥ 1] → 0
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2), let $M=M(T)$ satisfy Slow Growth Condition 1, and let $X_{\xi_T}$ be the ON-period that starts at the last renewal epoch $T_{\xi_T-1}$ in $[0,T]$ (defined on $\{\xi_T\ge1\}$). Then for every $\delta>0$,
--   $$M\,[b(MT)]^{-1}\,E\Bigl[X_{\xi_T}\mathbf 1_{[X_{\xi_T}>\delta b(MT)]}\mathbf 1_{[\xi_T\ge1]}\Bigr]\to0\qquad(T\to\infty).$$
--
--   This truncation estimate is the auxiliary result behind Lemma 6.
--
--   **Formalization Note.** The statement also asserts that the random variable inside the expectation is integrable for every $T$ (the page uses its expectation as a real number), so the Bochner integral's junk value $0$ for non-integrable functions cannot make the limit trivial. The indicator $\mathbf 1_{[\xi_T\ge1]}$ is built into `Xlast`, which is $0$ when $\xi_T=0$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 43, Lemma 5

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_5
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) (δ : ℝ) (hδ : 0 < δ) :
    (∀ T, Integrable (fun ω =>
      if δ * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < s.Xlast T ω then s.Xlast T ω else 0) P) ∧
    Tendsto (fun T => (M T : ℝ) * (NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T))⁻¹ *
      ∫ ω, (if δ * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < s.Xlast T ω then s.Xlast T ω else 0) ∂P)
      atTop (𝓝 0) := by sorry

end NetTraffic.OnOffStable
