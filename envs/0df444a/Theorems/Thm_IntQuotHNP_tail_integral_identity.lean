-- Prove2me | Theorems.Thm_IntQuotHNP_tail_integral_identity
-- name    : IntQuotHNP.tail_integral_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:30.373939+00:00
-- url     : https://prove2.me/theorems/0b830948-9549-41c6-936c-7b19bcb1c5e3
-- title:
--   §3.3 — tail-integral identity $E[\min\{T,Z^k\}]=1+k\int_1^{T^{1/k}}u^{k-1}\Pr[Z>u]\,du$
-- statement:
--   For a random variable $Z\ge1$ on a probability space, a real $T\ge1$ and an integer $k\ge1$,
--   $$
--   E[\min\{T,Z^k\}]=1+\int_1^T\Pr[Z>t^{1/k}]\,dt=1+k\int_1^{T^{1/k}}u^{k-1}\Pr[Z>u]\,du .
--   $$
--   This turns the expected size of the search into an integral of the tail of $Z_{\mathrm{target}}$.
--
--   Differences from the source:
--   - encoding: a random variable Z ≥ 1 → a measurable Z with Z ≥ 1 almost surely, and Pr[·] as μ(·).toReal; reason: the usual meaning of the source's words, which covers the pointwise case
--   - encoding: k with no stated range → k a natural number ≥ 1; reason: in the source k is the number of error variables, and t^{1/k} needs k ≠ 0
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.3, p.21 (PDF p.22)

import Mathlib

open MeasureTheory

namespace IntQuotHNP

/-- **§3.3: the tail-integral identity `E[min{T, Z^k}] = 1 + k∫_1^{T^{1/k}} u^{k−1} Pr[Z > u] du`.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §3.3, p.21 (PDF p.22): "For any random variable Z ≥ 1 and real T ≥ 1, the tail-integral
identity and the substitution t = u^k give E[min{T, Z^k}] = 1 + ∫_1^T Pr[Z > t^{1/k}] dt
= 1 + k ∫_1^{T^{1/k}} u^{k−1} Pr[Z > u] du."

For a random variable `Z ≥ 1` on a probability space, a real `T ≥ 1` and an integer `k ≥ 1`, both
equalities hold.

**Formalization Note.** `Pr[Z > s]` is `μ{ω : s < Z ω}` as a real number; `t^{1/k}` is `Real.rpow`.
`k` is the number of error variables, a positive integer. `Z ≥ 1` is read almost surely, which
covers the pointwise case. -/
theorem tail_integral_identity {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZm : Measurable Z) (hZ : ∀ᵐ ω ∂μ, 1 ≤ Z ω) (T : ℝ)
    (hT : 1 ≤ T) (k : ℕ) (hk : 1 ≤ k) :
    ∫ ω, min T (Z ω ^ k) ∂μ =
        1 + ∫ t in (1 : ℝ)..T, (μ {ω | t ^ (1 / (k : ℝ)) < Z ω}).toReal ∧
      ∫ ω, min T (Z ω ^ k) ∂μ =
        1 + k * ∫ u in (1 : ℝ)..T ^ (1 / (k : ℝ)), u ^ (k - 1) * (μ {ω | u < Z ω}).toReal := by sorry

end IntQuotHNP
