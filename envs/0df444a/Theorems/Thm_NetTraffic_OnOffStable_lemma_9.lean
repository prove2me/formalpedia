-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_9
-- name    : NetTraffic.OnOffStable.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:16.388982+00:00
-- url     : https://prove2.me/theorems/0ed9b092-25e3-462a-bbdd-a3d4dbc33d8c
-- title:
--   Lemma 9, p. 50 — M P(S_{[μ_T]} ≤ −x b(MT)) → 0
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2) and let $M=M(T)$ satisfy Slow Growth Condition 1. With $S_n=\sum_{k=1}^nJ_k$, $J_k=r_{\mathrm{on}}(X_k-\mu_{\mathrm{on}})-r_{\mathrm{off}}(Y_k-\mu_{\mathrm{off}})$ and $\mu_T=T/\mu$, for every $x>0$,
--   $$M\,P\bigl(S_{[\mu_T]}\le -x\,b(MT)\bigr)=o(1)\qquad(T\to\infty).$$
--
--   This is the left-tail estimate behind condition (B) in the proof of Lemma 10; it uses $\alpha<\alpha_{\mathrm{off}}$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 50, Lemma 9

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_9
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun T => (M T : ℝ) *
      P.real {ω | s.S Fon Foff ⌊muT Fon Foff T⌋₊ ω ≤ -(x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T))})
      atTop (𝓝 0) := by sorry

end NetTraffic.OnOffStable
