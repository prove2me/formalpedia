-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_3_6
-- name    : MemOracleLB.Optimization.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:16.016594+00:00
-- url     : https://prove2.me/theorems/fdf8dccb-756d-4580-b7bf-e932b238cdb6
-- title:
--   Lemma 3.6 — Entropy removed by a random projection
-- statement:
--   Let $d\ge2$ and let $\mu$ be a probability measure on $E_d$ with finite $K(\mu)$. Let $V$ be a random unit vector of law $\rho$ satisfying $\mathbb EVV^\top\succeq\delta I_d$ for $\delta>0$. Then the projected-entropy function is measurable and
--
--   $$\mathbb E_VD_{\rm KL}((P_{V^\perp})_\#\mu\|\gamma_{V^\perp})\le(1-\delta)K(\mu).$$
--
--   The second-moment comparison means $\int\langle w,v\rangle^2\,d\rho(v)\ge\delta\|w\|^2$ for every $w$. The law is supported on the unit sphere almost surely. No log-concavity is required.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: Gaussian reference on the varying subspace V-perp → both pushed-forward measures on the fixed ambient Euclidean space; reason: this is exactly k(P) in the source proof on PDF p.16 and gives the same divergence
--   - encoding: an expectation of projected entropy → a nonnegative integral with measurability asserted in the conclusion; reason: this prevents interpreting the expectation as a lower integral of a nonmeasurable function
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 3.6, PDF p. 16 (printed p. 15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 3.6, PDF p.16 (printed p.15). The projected entropy is measurable as well as bounded in mean. -/
theorem lemma_3_6 {d : ℕ} (hd : 2 ≤ d) (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hK : gaussianEntropy μ ≠ ⊤) (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    (hunit : ∀ᵐ v ∂ρ, ‖v‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hspread : ∀ w : E d, δ * ‖w‖ ^ 2 ≤ ∫ v, ⟪w, v⟫ ^ 2 ∂ρ) :
    Measurable (projectedEntropy μ) ∧
    (∫⁻ v, projectedEntropy μ v ∂ρ) ≤ ENNReal.ofReal (1 - δ) * gaussianEntropy μ := by sorry

end MemOracleLB.Optimization
