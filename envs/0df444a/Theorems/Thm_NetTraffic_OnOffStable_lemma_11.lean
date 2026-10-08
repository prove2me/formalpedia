-- Prove2me | Theorems.Thm_NetTraffic_OnOffStable_lemma_11
-- name    : NetTraffic.OnOffStable.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:24.805011+00:00
-- url     : https://prove2.me/theorems/f8e7ecd5-1ede-4154-a883-c6769982da5c
-- title:
--   Lemma 11, p. 53 — M P(Z⁽¹⁾_T + Z⁽²⁾_T > x b(MT)) → (r_on^α/μ)[b₁^α 1[b₁>0] t₁ + b₂^α 1[b₂>0](t₂ − t₁)] x^{−α}
-- statement:
--   Let a single stationary ON/OFF source satisfy (2.1)–(2.2) and let $M=M(T)$ satisfy Slow Growth Condition 1. Let $b_1,b_2\in\mathbb R$ and $t_2\ge t_1\ge0$, $\mu_{Tt}=Tt/\mu$, and
--   $$Z^{(1)}_T=b_1\sum_{k=1}^{[\mu_{Tt_1}]}J_k,\qquad Z^{(2)}_T=b_2\sum_{k=[\mu_{Tt_1}]+1}^{[\mu_{Tt_2}]}J_k .$$
--   Then for every $x>0$, as $T\to\infty$, both
--   $$M\,P\bigl(Z^{(1)}_T+Z^{(2)}_T>x\,b(MT)\bigr)\quad\text{and}\quad M\,P\bigl(Z^{(1)}_T>x\,b(MT)\bigr)+M\,P\bigl(Z^{(2)}_T>x\,b(MT)\bigr)$$
--   converge to
--   $$\frac{r_{\mathrm{on}}^\alpha}{\mu}\Bigl[b_1^\alpha\mathbf 1_{[b_1>0]}t_1+b_2^\alpha\mathbf 1_{[b_2>0]}(t_2-t_1)\Bigr]x^{-\alpha}.$$
--
--   This tail computation for linear combinations of increments is the key to the two-dimensional distributions in Lemma 12.
--
--   **Formalization Note.** The page writes the upper summation limits as $\mu_{Tt_1}$, $\mu_{Tt_2}$, which need not be integers; they are read as integer parts, as everywhere else in §5. The page's chain "$\sim\ldots\sim$ constant" is read as: both quantities converge to the constant (which can be $0$). Here $b_1,b_2$ are real coefficients, not the quantile function $b$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 53, Lemma 11 (upper limits read as integer parts)

import Mathlib
import Definitions.Def_NetTraffic_OnOffStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

theorem lemma_11
    {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    {M : ℝ → ℕ} (hM : SourceCount M) (hC1 : Condition1 Fon M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s)
    (b₁ b₂ t₁ t₂ : ℝ) (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (x : ℝ) (hx : 0 < x) :
    let Z1 : ℝ → Ω → ℝ := fun T ω =>
      b₁ * ∑ k ∈ Finset.range ⌊muT Fon Foff (T * t₁)⌋₊, s.J Fon Foff k ω
    let Z2 : ℝ → Ω → ℝ := fun T ω =>
      b₂ * ∑ k ∈ Finset.Ico ⌊muT Fon Foff (T * t₁)⌋₊ ⌊muT Fon Foff (T * t₂)⌋₊, s.J Fon Foff k ω
    let L : ℝ := rOn Fon Foff ^ α / mu Fon Foff *
      ((if 0 < b₁ then b₁ ^ α else 0) * t₁ + (if 0 < b₂ then b₂ ^ α else 0) * (t₂ - t₁)) *
      x ^ (-α)
    Tendsto (fun T => (M T : ℝ) *
        P.real {ω | x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < Z1 T ω + Z2 T ω}) atTop (𝓝 L) ∧
    Tendsto (fun T => (M T : ℝ) * P.real {ω | x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < Z1 T ω} +
        (M T : ℝ) * P.real {ω | x * NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) < Z2 T ω}) atTop (𝓝 L) := by sorry

end NetTraffic.OnOffStable
