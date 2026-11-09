-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_3_5
-- name    : MemOracleLB.Optimization.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:57.504775+00:00
-- url     : https://prove2.me/theorems/653e9508-e9ab-47f1-a024-9f4e288c92cf
-- title:
--   Lemma 3.5 — Normalization
-- statement:
--   Let $d\ge1$, $0<\varepsilon\le1/2$, and let independent rows $X_1,\ldots,X_d\in E_d$ have probability laws $\mu_i$ of finite Gaussian relative entropy. There are replacement independent row laws $\mu'_i$ such that every individual flip is preserved and the total Gaussian entropy does not increase:
--
--   $$\nu_i(\mu')=\nu_i(\mu)\quad\text{for all }i,\qquad \sum_i K(\mu'_i)\le\sum_iK(\mu_i).$$
--
--   The replacement laws have finite second moments $M_i=\mathbb E X_iX_i^\top$ and satisfy both conclusions of equation (5):
--
--   $$M_i=d\,\mathbb E\frac{X_iX_i^\top}{\|X_i\|^2},\qquad \left\|\frac1d\sum_iM_i-I_d\right\|_{\rm op}\le\varepsilon.$$
--
--   No log-concavity assumption is imposed. Independence is the product of the replacement laws, and finite input entropy ensures that the entropy comparison also makes every replacement entropy finite.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: second-moment matrices and their operator norm → Bochner-integrated rank-one continuous linear operators with finite second moments in the conclusion; reason: these are the same finite-dimensional operators, and the moment condition excludes nonintegrable default values
--   - encoding: division by the squared row length → the value zero at the zero vector; reason: finite Gaussian entropy gives absolute continuity, so the zero row has probability zero
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 3.5, PDF p. 14 (printed p. 13), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 3.5, PDF p.14 (printed p.13). Entropy, every individual flip, and both parts of (5). -/
theorem lemma_3_5 {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (μ : Fin d → Measure (E d)) [∀ i, IsProbabilityMeasure (μ i)]
    (hK : ∀ i, gaussianEntropy (μ i) ≠ ⊤) :
    ∃ μ' : Fin d → Measure (E d),
      (∀ i, IsProbabilityMeasure (μ' i)) ∧
      (∀ i, flip μ' i = flip μ i) ∧
      (∑ i, gaussianEntropy (μ' i)) ≤ ∑ i, gaussianEntropy (μ i) ∧
      (∀ i, SecondMomentFinite (μ' i)) ∧
      (∀ i, momentOperator (μ' i) = (d : ℝ) • angularMomentOperator (μ' i)) ∧
      ‖(d : ℝ)⁻¹ • (∑ i, momentOperator (μ' i)) -
        ContinuousLinearMap.id ℝ (E d)‖ ≤ ε := by sorry

end MemOracleLB.Optimization
