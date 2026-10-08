-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_lemma_13
-- name    : NetTraffic.OnOffFBM.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:33.546705+00:00
-- url     : https://prove2.me/theorems/02ccf2ba-488d-4cb9-93ee-dea68257fa65
-- title:
--   Lemma 13 (7.3), p. 62 — d_T^{−1} Σ_m G^{(m)}_{Tt} →d N(0, σ₀² t^{3−α}) =d σ₀ B_H(t)
-- statement:
--   Consider the superposition of $M=M(T)$ independent stationary ON/OFF sources with period laws satisfying (2.1)–(2.2), $M$ non-decreasing with $M(T)\to\infty$, and assume Fast Growth Condition 2. Let $G^{(m)}_T=\int_0^T(W^{(m)}_u-EW^{(m)}_u)\,du$ be the centred cumulative workload of source $m$ and $d_T=[T^{3-\alpha}L_{\mathrm{on}}(T)M]^{1/2}$. Then for every $t\ge0$,
--   $$d_T^{-1}\sum_{m=1}^MG^{(m)}_{Tt}\ \xrightarrow{d}\ N(0,\sigma_0^2t^{3-\alpha})\qquad(T\to\infty),$$
--   and $N(0,\sigma_0^2t^{3-\alpha})$ is the law of $\sigma_0B_H(t)$ for every standard fractional Brownian motion $B_H$ with $H=(3-\alpha)/2$.
--
--   This is the one-dimensional case of the finite-dimensional convergence in Theorem 4.
--
--   **Formalization Note** $N(0,v)$ is Mathlib's `gaussianReal 0 v`; at $t=0$ it is the point mass at $0$. Each model $T$ has its own probability space. The second claim is stated for standard fractional Brownian motions on any probability space.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 62, Lemma 13, (7.3)

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- Lemma 13, (7.3), p. 62: under Condition 2, for every `t ≥ 0`,
`d_T^{-1} Σ_{m=1}^M G^{(m)}_{Tt} →d N(0, σ_0² t^{3-α})`, and `N(0, σ_0² t^{3-α})` is the law of
`σ_0 B_H(t)` for a standard fractional Brownian motion `B_H`, `H = (3-α)/2`. -/
theorem lemma_13
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∀ t : ℝ≥0,
      TendstoInDistribution
        (fun T ω => (dT Fon α M T)⁻¹ *
          ∑ m ∈ Finset.range (M T), (src T m).G (P T) (T * t) ω)
        atTop id P (gaussianReal 0 (sigma0sq Fon Foff α * (t : ℝ) ^ (3 - α)).toNNReal) ∧
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
        (B : ℝ≥0 → Ω' → ℝ), IsStdFBM (hurst α) B Q →
          Q.map (fun ω => sigma0 Fon Foff α * B t ω) =
            gaussianReal 0 (sigma0sq Fon Foff α * (t : ℝ) ^ (3 - α)).toNNReal := by sorry

end NetTraffic.OnOffFBM
