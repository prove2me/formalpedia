-- Prove2me | Theorems.Thm_IntegerSumAmplification_Main_lemma_6_5
-- name    : IntegerSumAmplification.Main.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:04:14.036069+00:00
-- url     : https://prove2.me/theorems/8d8d52de-9838-41f4-9c91-a746b43b8193
-- title:
--   Lemma 6.5 — Empirical quantile decoder
-- statement:
--   Let $D$ and the integer-valued sum predictor $A$ have the residual setting above, with $k>0$ and sum-prediction success at least $\varepsilon$. Let $L\ge1$, $0\le\theta<\varepsilon/2$, and $0<u<\varepsilon/2-\theta$, and put $g=\varepsilon/2-\theta-u$. For any fixed level $\widehat\psi$ satisfying $|\widehat\psi-\psi|\le\theta$, set $j=\lceil L\widehat\psi\rceil$ and draw $L$ independent restrictions, independently of the test pair. Then $1\le j\le L$ and
--   $$\Pr[H_j(X)\ne Y]\le\frac1{2ku^2}+2e^{-2Lg^2}.$$
--   The same error bound holds for every random real level $\widehat\Psi$ independent of the restrictions and the test pair, with $|\widehat\Psi-\psi|\le\theta$ almost surely. Its random rank lies in $\{1,\ldots,L\}$ almost surely. All order statistics retain multiplicities.
--
--   Differences from the source:
--   - encoding: binary words and one-based coordinates → Fin-indexed bits, little-endian decoding, and block concatenation; reason: these are bijective encodings; invalid output codes remain failures
--   - encoding: independent samples from D → the product probability measure D^k; reason: integration and event measures give exactly the stated expectations and probabilities
--   - encoding: a uniform coordinate and samples outside that coordinate → normalized counting measure on Fin k times D^k, ignoring the selected sample; reason: the extra unused sample integrates out and changes no residual distribution
--   - encoding: an independent random level → every probability law ν on the real line, with joint law ν times the decoder experiment; reason: independence is exactly the product-law identity, so every source random level is covered
--   - encoding: j = ceil(L times the level) → the natural ceiling, with 1 ≤ j ≤ L asserted; reason: the source assumptions force a positive level; no invalid-rank default is used
--   - generalization: the surrounding reconstruction application uses 0 < ε < 1 → only the printed θ and u conditions and the success premise; reason: these imply ε > 0 and ε ≤ 1; no upper strict bound is needed, so perfect prediction is included
-- source:
--   Farhan Ali and Weiqiang Yuan, Optimal Black-Box Hardness Amplification for Integer Sums, held manuscript dated November 3, 2026 (STOC 2027 submission; acceptance not asserted); citation_basis: published. Lemma 6.5, printed pp. 15–16 / PDF pp. 18–19; §6.1 context printed p. 12 / PDF p. 15. PDF SHA256 181fd8ae5069b0c062ebccc0aa72d5a78ec0c836e6d8f6f99dd60464c0b746d7.

import Definitions.Def_IntegerSumAmplification_Main_OrderStatistic
open MeasureTheory

namespace IntegerSumAmplification.Main

theorem lemma_6_5 {n m k L : ℕ} (hk : 0 < k) (hL : 0 < L)
    (D : Measure (LabeledInput n m)) [IsProbabilityMeasure D]
    (A : (Fin k → Bits n) → ℤ) (ε θ u : ℝ)
    (hA : ε ≤ (productLaw D k).real {z | globalResidual A z = 0})
    (hθ : 0 ≤ θ ∧ θ < ε / 2) (hu : 0 < u ∧ u < ε / 2 - θ) :
    (∀ level : ℝ, |level - targetLevel D A| ≤ θ →
      (1 ≤ quantileRank L level ∧ quantileRank L level ≤ L) ∧
      (decodingLaw D k L).real {z |
        quantileDecoder A z.1 (quantileRank L level) z.2.1 ≠ (z.2.2.val : ℤ)} ≤
        1 / (2 * (k : ℝ) * u ^ 2) + 2 * Real.exp (-2 * (L : ℝ) * (ε / 2 - θ - u) ^ 2)) ∧
    (∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      (∀ᵐ level ∂ν, |level - targetLevel D A| ≤ θ) →
      (∀ᵐ level ∂ν, 1 ≤ quantileRank L level ∧ quantileRank L level ≤ L) ∧
      (ν.prod (decodingLaw D k L)).real {z |
        quantileDecoder A z.2.1 (quantileRank L z.1) z.2.2.1 ≠ (z.2.2.2.val : ℤ)} ≤
        1 / (2 * (k : ℝ) * u ^ 2) + 2 * Real.exp (-2 * (L : ℝ) * (ε / 2 - θ - u) ^ 2)) := by sorry

end IntegerSumAmplification.Main
