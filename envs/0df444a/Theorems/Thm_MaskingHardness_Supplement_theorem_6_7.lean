-- Prove2me | Theorems.Thm_MaskingHardness_Supplement_theorem_6_7
-- name    : MaskingHardness.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:52.942173+00:00
-- url     : https://prove2.me/theorems/25c80c5d-9f2d-40aa-9886-4b37efe79956
-- title:
--   Theorem 6.7 — hardcore measures from multicalibration [CDV24, CGKR25]
-- statement:
--   For all finite $\mathcal X$, distributions over $(x,y)\in\mathcal X\times\{\pm1\}$, finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R\}$ and models $p:\mathcal X\to[-1,1]$, define $\mu:\{\pm1\}\times[-1,1]\to[0,1]$ by
--
--   $$
--   \mu(y,z)=\frac{1-yz}{1+|z|}.
--   $$
--
--   Then:
--
--   1. **(Hardness $\ge$ Density)** if $\displaystyle \mathbb E\Big[\frac{c(x)}{1+|p(x)|}\big(y-p(x)\big)\Big]\le\varepsilon_2$ for all $c\in\mathcal C$, then $\mathbb E[(1-c(x)y)_+]\ge\mathbb E[\mu(y,p(x))]-\varepsilon_2$ for all $c\in\mathcal C$;
--   2. **(Hardness $\le$ Density)** if $\displaystyle \mathbb E\Big[\frac{\mathrm{sign}(p(x))}{1+|p(x)|}\big(y-p(x)\big)\Big]\ge-\varepsilon_3$, then $\mathbb E[(1-\mathrm{sign}(p(x))y)_+]\le\mathbb E[\mu(y,p(x))]+\varepsilon_3$.
--
--   This recovers the construction of a hardcore measure from a weighted-multiaccurate and calibrated predictor in the binary setting.
--
--   **Formalization Note** $\mathrm{sign}$ is `Real.sign` with $\mathrm{sign}(0)=0$; the hypotheses are one-sided, as printed.
--
--   Differences from the source:
--   - encoding: labels y ∈ {±1} → Bool, with real value signVal y = ±1 in every formula; reason: a two-element label type; only the values ±1 are used
--   - encoding: a distribution over (x, y) ∈ X × Y → weights D x y with IsDist D (nonnegative, summing to 1), expectations as weighted finite sums; reason: the same distributions; zero-probability pairs allowed
--   - encoding: a finite class C ⊆ {X → ℝ} and c_λ = ∑_{c∈C} λ_c c → a finite indexed family c : ι → X → ℝ with c_λ(x) = ∑ᵢ λᵢ cᵢ(x); reason: an indexed family with ι = C recovers the set; repeated members change neither side
--   - reading: sign(p(x)), with sign(0) not specified by the source → Real.sign (p x), so sign(0) = 0; reason: the source never fixes sign(0); the pointwise identity (1 − s·y)₊ − µ(y, 0) = −s·y behind (b) holds for every s ∈ {−1, 0, 1}, so (b) is true under each convention, and sign(0) = 0 is the standard one
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 6.7, p.33 (PDF p.35); proof pp.33–35 (PDF pp.35–37)

import Mathlib
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_Supplement_signVal

namespace MaskingHardness.Supplement

/-- **Theorem 6.7** ([CDV24, CGKR25]) (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 6.7, printed p.33 = PDF p.35; proof printed
pp.33–35 = PDF pp.35–37).

For all finite `X`, distributions over `(x, y) ∈ X × {±1}`, finite `C ⊆ {X → ℝ}` and models
`p : X → [−1, +1]`, define `µ(y, z) = (1 − yz)/(1 + |z|)`. Then
(a) if `∀ c ∈ C, E[c(x)/(1 + |p(x)|) · (y − p(x))] ≤ ε2`, then
`∀ c ∈ C, E[(1 − c(x)y)₊] ≥ E[µ(y, p(x))] − ε2`;
(b) if `E[sign(p(x))/(1 + |p(x)|) · (y − p(x))] ≥ −ε3`, then
`E[(1 − sign(p(x))y)₊] ≤ E[µ(y, p(x))] + ε3`.

**Formalization Note** Labels are `Bool` with real value `signVal y = ±1`; `D` is given by weights;
`C` is an indexed family `c : ι → X → ℝ`; `sign` is `Real.sign` (`sign 0 = 0`); `(t)₊ = max 0 t`. The
hypotheses are one-sided, as printed. -/
theorem theorem_6_7 {X ι : Type*} [Fintype X] [Fintype ι]
    (D : X → Bool → ℝ) (hD : IsDist D) (c : ι → X → ℝ)
    (p : X → ℝ) (hp : ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1) (ε₂ ε₃ : ℝ) :
    ((∀ i, ∑ x, ∑ y, D x y * (c i x / (1 + |p x|) * (signVal y - p x)) ≤ ε₂) →
      ∀ i, ∑ x, ∑ y, D x y * ((1 - signVal y * p x) / (1 + |p x|)) - ε₂ ≤
        ∑ x, ∑ y, D x y * max 0 (1 - c i x * signVal y)) ∧
    (-ε₃ ≤ ∑ x, ∑ y, D x y * (Real.sign (p x) / (1 + |p x|) * (signVal y - p x)) →
      ∑ x, ∑ y, D x y * max 0 (1 - Real.sign (p x) * signVal y) ≤
        ∑ x, ∑ y, D x y * ((1 - signVal y * p x) / (1 + |p x|)) + ε₃) := by sorry

end MaskingHardness.Supplement
