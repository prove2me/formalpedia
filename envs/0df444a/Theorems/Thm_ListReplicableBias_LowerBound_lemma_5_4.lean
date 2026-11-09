-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_lemma_5_4
-- name    : ListReplicableBias.LowerBound.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:24.137054+00:00
-- url     : https://prove2.me/theorems/70d0088c-9007-4f20-980d-832bf72c95ae
-- title:
--   Lemma 5.4 — Bernoulli likelihood-ratio identity and exponential bound
-- statement:
--   Let $p,q\in(0,1)$, $R=\operatorname{Bern}(p)$ and $S=\operatorname{Bern}(q)$. Then
--   $$\mathbb E_R\!\left[\left(\frac{dS}{dR}\right)^2\right]=1+\frac{(p-q)^2}{p(1-p)}.$$
--   In particular, if $1/4\le p\le3/4$, then
--   $$\mathbb E_R\!\left[\left(\frac{dS}{dR}\right)^2\right]\le\exp\!\left(\frac{16}{3}(p-q)^2\right).$$
--   Both assertions are included. They quantify the one-toss change of measure used in the adaptive transcript estimate.
--
--   Differences from the source:
--   - encoding: $\mathbb E_R[(dS/dR)^2]$ → $\sum_{x\in\{0,1\}}S(x)^2/R(x)$; reason: both masses of R are strictly positive for the stated p domain, so this is exactly the expectation
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Lemma 5.4, PDF p. 5

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Lemma 5.4, PDF p. 5: both the identity and its exponential consequence.
The finite sum is exactly the expectation since both R masses are positive. -/
theorem lemma_5_4 (p q : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ x : Bool, bernMass q x ^ 2 / bernMass p x) =
      1 + (p - q) ^ 2 / (p * (1 - p)) ∧
    (p ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) →
      (∑ x : Bool, bernMass q x ^ 2 / bernMass p x) ≤
        Real.exp ((16 / 3 : ℝ) * (p - q) ^ 2)) := by sorry

end ListReplicableBias.LowerBound
