-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_4
-- name    : NetTraffic.OnOffStable.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:13.000473+00:00
-- url     : https://prove2.me/theorems/9dc125f1-b96e-4bfa-bfb0-dba44298254f
-- title:
--   Lemma 4, p. 42 — under (5.3), M P(|ξ_T − μ_T| > ε_T μ_T) → 0
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2), let $M=M(T)$ satisfy Slow Growth Condition 1, and let $\xi_T=\sum_{n\ge0}\mathbf 1_{[0,T]}(T_n)$ be the number of renewal epochs of the source in $[0,T]$, with mean $\mu_T=T/\mu$. Let $\varepsilon_T\to0$ satisfy (5.3):
--   $$b(MT)=o(\varepsilon_T T)\quad\text{and}\quad 1/\log T=o(\varepsilon_T)\qquad(T\to\infty).$$
--   Then
--   $$M\,P\bigl(|\xi_T-\mu_T|>\varepsilon_T\mu_T\bigr)=o(1)\qquad(T\to\infty).$$
--
--   The lemma lets the random counts $\xi^{(m)}_T$ be replaced by their common mean $\mu_T$ simultaneously for all $M$ sources; it is used in Lemmas 5, 6, 10 and 12.
--
--   **Formalization Note.** $\varepsilon_T$ is a positive function ($\varepsilon_T>0$ for every $T$): the page's tolerance $\varepsilon_T\mu_T$, its example $\varepsilon_T=(b(MT)/T)^{1/2}\vee(\log T)^{-1/2}$ and its proof ($(1+\varepsilon_T)\mu_T$) all take it positive, and without the sign the hypotheses (5.3) are also met by $-\varepsilon_T$, for which the event is almost sure and the claim false. The two $o(\cdot)$ relations of (5.3) are Mathlib's little-o (`=o[atTop]`); "$=o(1)$" is convergence to $0$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 42, (5.3) and Lemma 4

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_4
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s)
    (ε : ℝ → ℝ) (hεpos : ∀ T, 0 < ε T) (hε : Tendsto ε atTop (𝓝 0))
    (h53a : (fun T => NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)) =o[atTop] (fun T => ε T * T))
    (h53b : (fun T => 1 / Real.log T) =o[atTop] ε) :
    Tendsto (fun T => (M T : ℝ) *
      P.real {ω | ε T * muT Fon Foff T < |(s.xi T ω : ℝ) - muT Fon Foff T|}) atTop (𝓝 0) := by sorry

end NetTraffic.OnOffStable
