-- Prove2me | Theorems.Thm_LaconicBarrier_lemma_4_34
-- name    : LaconicBarrier.lemma_4_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:12.794726+00:00
-- url     : https://prove2.me/theorems/785d93db-975d-4f30-a176-39ede5de0ece
-- title:
--   Lemma 4.34 — tail bound for $k$-wise independent sums
-- statement:
--   Let $k \ge 4$ be an even integer and let $X_1, \dots, X_v$ be $k$-wise independent random variables with values in $[0,1]$. Put $Z = \sum_{j=1}^v X_j$ and $\mu = \mathbb E[Z]$. Then for every $\tau > 0$,
--   $$
--   \Pr\bigl[|Z - \mu| \ge \tau\bigr] \le 8\left(\frac{k\mu + k^2}{\tau^2}\right)^{k/2}.
--   $$
--
--   This is the concentration bound behind the bucket-hashing step of the proof of Theorem 5.1, where the hash family is only $(2d+1)$-wise independent.
--
--   Differences from the source:
--   - encoding: random variables with values in [0, 1] → measurable real functions on a probability space with values in [0, 1] everywhere; k/2 natural-number division; reason: random variables are measurable; k is even
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 4.34, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep

namespace LaconicBarrier

open MeasureTheory ProbabilityTheory

/-- **Lemma 4.34** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Lemma 4.34, p.28, after [BR94, Lemma 2.3]): let `k ≥ 4` be even and let
`X₁, …, X_v` be `k`-wise independent random variables with values in `[0, 1]`; put `Z = ∑_j X_j` and
`µ = E[Z]`. Then for every `τ > 0`, `Pr[|Z − µ| ≥ τ] ≤ 8 ((kµ + k²)/τ²)^{k/2}`.

**Formalization Note** Random variables are measurable functions on a probability space; `k/2` is
an integer since `k` is even. -/
theorem lemma_4_34 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k v : ℕ) (hk : 4 ≤ k) (hkeven : Even k) (X : Fin v → Ω → ℝ) (hmeas : ∀ j, Measurable (X j))
    (hind : KWiseIndep μ X k) (hrange : ∀ j ω, X j ω ∈ Set.Icc (0 : ℝ) 1) (τ : ℝ) (hτ : 0 < τ) :
    μ.real {ω | τ ≤ |∑ j, X j ω - ∫ ω', (∑ j, X j ω') ∂μ|} ≤
      8 * (((k : ℝ) * (∫ ω', (∑ j, X j ω') ∂μ) + (k : ℝ) ^ 2) / τ ^ 2) ^ (k / 2) := by sorry

end LaconicBarrier
