-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_eq_7_4
-- name    : NetTraffic.OnOffFBM.eq_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:42.162513+00:00
-- url     : https://prove2.me/theorems/2bea4883-8939-4574-81ba-fe6fbd1105ef
-- title:
--   (7.4), p. 62 — M d_T^{−2} Cov(G_{Tt₁}, G_{Tt₂}) → (σ₀²/2)[t₁^{2H} + t₂^{2H} − (t₂ − t₁)^{2H}]
-- statement:
--   Let $W$ be the stationary ON/OFF process of one source with period laws satisfying (2.1)–(2.2), $G_T=\int_0^T(W_u-EW_u)\,du$, let $M=M(T)$ be non-decreasing with $M(T)\to\infty$, assume Fast Growth Condition 2, and let $d_T=[T^{3-\alpha}L_{\mathrm{on}}(T)M]^{1/2}$ and $H=(3-\alpha)/2$. Then for $0\le t_1\le t_2$, as $T\to\infty$,
--   $$M d_T^{-2}\,\mathrm{Cov}(G_{Tt_1},G_{Tt_2})\to\frac{\sigma_0^2}2\big[t_1^{2H}+t_2^{2H}-(t_2-t_1)^{2H}\big],$$
--   and the right-hand side equals $\mathrm{Cov}(\sigma_0B_H(t_1),\sigma_0B_H(t_2))$ for every standard fractional Brownian motion $B_H$.
--
--   Together with Lemma 13 this identifies the limits of the finite-dimensional distributions in Theorem 4 as those of $\sigma_0B_H$.
--
--   **Formalization Note** The second claim is stated for standard fractional Brownian motions on any probability space.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 62, (7.4)

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- (7.4), p. 62: under Condition 2, for `t_1 ≤ t_2`, as `T → ∞`,
`M d_T^{-2} Cov(G_{Tt_1}, G_{Tt_2}) → (σ_0²/2)[t_1^{2H} + t_2^{2H} - (t_2 - t_1)^{2H}]`, which is
`Cov(σ_0 B_H(t_1), σ_0 B_H(t_2))` for a standard fractional Brownian motion, `H = (3-α)/2`. -/
theorem eq_7_4
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M) :
    ∀ t₁ t₂ : ℝ≥0, t₁ ≤ t₂ →
      Tendsto (fun T => (M T : ℝ) / dT Fon α M T ^ 2 *
          cov[s.G P (T * t₁), s.G P (T * t₂); P])
        atTop (𝓝 (sigma0sq Fon Foff α / 2 * ((t₁ : ℝ) ^ (2 * hurst α) + (t₂ : ℝ) ^ (2 * hurst α)
          - ((t₂ : ℝ) - t₁) ^ (2 * hurst α)))) ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
        (B : ℝ≥0 → Ω' → ℝ), IsStdFBM (hurst α) B Q →
          cov[fun ω => sigma0 Fon Foff α * B t₁ ω, fun ω => sigma0 Fon Foff α * B t₂ ω; Q] =
            sigma0sq Fon Foff α / 2 * ((t₁ : ℝ) ^ (2 * hurst α) + (t₂ : ℝ) ^ (2 * hurst α)
              - ((t₂ : ℝ) - t₁) ^ (2 * hurst α)) := by sorry

end NetTraffic.OnOffFBM
