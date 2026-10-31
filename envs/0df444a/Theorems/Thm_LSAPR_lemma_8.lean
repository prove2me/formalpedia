-- Prove2me | Theorems.Thm_LSAPR_lemma_8
-- name    : LSAPR.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:53.849994+00:00
-- url     : https://prove2.me/theorems/44ed5e6d-49a8-4f5c-be84-991fb37cf353
-- title:
--   Lemma 8 — Hoeffding's inequality for independent centered bounded random vectors (Pinelis)
-- statement:
--   Let $X_1,\dots,X_n$ be independent random vectors of $\mathbb R^d$ with $\mathbb E[X_i]=0$ and $\|X_i\|\le\beta_i$ almost surely. Then for every $t\ge0$,
--   $$\mathbb P\Big(\Big\|\sum_{i=1}^nX_i\Big\|\ge t\Big)\le2\exp\Big\{-\frac{t^2}{2\sum_{j=1}^n\beta_j^2}\Big\}.$$
--
--   This is the dimension-free concentration bound behind Propositions 3 and 6. The norm is Euclidean.
--
--   Differences from the source:
--   - encoding: the exponent t²/(2Σβⱼ²), undefined when Σβⱼ² = 0 → Lean's t²/0 = 0, so the bound reads 2 in that case; reason: the only affected case is one where the printed formula has no meaning; the Lean bound is then trivially true and every case with Σβⱼ² > 0 is the source's
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Lemma 8, p.35 (Pinelis 1994, Theorem 3.5)

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Lemma 8 (Pinelis 1994, Theorem 3.5), arXiv:2207.04475v2, p.35: Hoeffding's inequality for
independent centered bounded random vectors `X₁, …, X_n` of `ℝ^d`, with the Euclidean norm.

**Formalization Note.** For `∑ β_j² = 0` the exponent is undefined in the paper and `t² / 0 = 0`
in Lean: the bound then reads `P(…) ≤ 2`, which is true. -/
theorem lemma_8 {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin n → Ω → Vec d) (β : Fin n → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ β i) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t ≤ ‖∑ i, X i ω‖} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * ∑ j, β j ^ 2))) := by sorry

end LSAPR
