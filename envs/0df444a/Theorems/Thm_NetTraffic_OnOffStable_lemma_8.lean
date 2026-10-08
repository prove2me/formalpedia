-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_8
-- name    : NetTraffic.OnOffStable.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:25.127334+00:00
-- url     : https://prove2.me/theorems/75974ea8-053d-4da2-994f-c0a58cb19d99
-- title:
--   Lemma 8, p. 49 — M P(|S_{T,1} − S_{[μ_T]}| > x b(MT), Θ_T) → 0
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2), let $M=M(T)$ satisfy Slow Growth Condition 1, and let $\varepsilon_T\to0$. With $J_k=r_{\mathrm{on}}(X_k-\mu_{\mathrm{on}})-r_{\mathrm{off}}(Y_k-\mu_{\mathrm{off}})$, $S_n=\sum_{k=1}^nJ_k$, $S_{T,1}=S_{\xi_T}$ and the event (5.11)
--   $$\Theta_T=\{|\xi_T-\mu_T|\le\varepsilon_T\mu_T\},$$
--   for every $x>0$,
--   $$M\,P\bigl(|S_{T,1}-S_{[\mu_T]}|>x\,b(MT),\ \Theta_T\bigr)=o(1)\qquad(T\to\infty).$$
--
--   On the event that the renewal count is close to its mean, replacing $\xi_T$ by $[\mu_T]$ in the random sum costs nothing at the scale $b(MT)$.
--
--   **Formalization Note.** As on the page, $\varepsilon_T$ is any function tending to $0$; no rate is assumed.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 49, (5.11) and Lemma 8

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_8
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun T => (M T : ℝ) *
      P.real ({ω | x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) <
          |s.ST Fon Foff T ω - s.S Fon Foff ⌊muT Fon Foff T⌋₊ ω|} ∩
        s.Theta Fon Foff ε T)) atTop (𝓝 0) := by sorry

end NetTraffic.OnOffStable
