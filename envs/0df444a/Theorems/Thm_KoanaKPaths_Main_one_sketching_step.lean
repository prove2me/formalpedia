-- Prove2me | Theorems.Thm_KoanaKPaths_Main_one_sketching_step
-- name    : KoanaKPaths.Main.one_sketching_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:03.246384+00:00
-- url     : https://prove2.me/theorems/02d8a025-5b4a-451e-8df6-265c237b0ce2
-- title:
--   Lemma 5 — one sketching step
-- statement:
--   Let $d,t,\ell$ be positive integers. Let $X$ be a random matrix in $\mathbb R^{d\times t}$ and let $R\in\{-1,1\}^{\ell\times d}$ be a random sign matrix, with mutually independent uniform entries, independent of $X$. Then
--   $$\mathbb E\bigl(\|RX\|_F^2\bigr)=\ell\,\mathbb E\bigl(\|X\|_F^2\bigr)\qquad\text{and}\qquad \mathbb E\bigl(\|RX\|_F^4\bigr)\le \ell^2\Bigl(1+\frac2\ell\Bigr)\mathbb E\bigl(\|X\|_F^4\bigr).$$
--   These bounds hold although all $t$ columns of $X$ are multiplied by the same matrix $R$.
--
--   This is the step that, applied once per layer of the recursive sketch, keeps the expected squared norm and increases the normalized fourth moment by at most the factor $1+2/\ell$.
--
--   **Formalization Note** $X$ and $R$ are measurable random variables on an arbitrary probability space; the law of $R$ is uniform on $\{-1,1\}^{\ell\times d}$ (equivalently, its entries are independent uniform signs) and $X,R$ are independent. The expectations are integrals in $[0,\infty]$, so $X$ need not have finite moments; when its moments are finite they are the ordinary expectations.
--
--   Differences from the source:
--   - encoding: expectations of the nonnegative random variables ‖RX‖_F², ‖RX‖_F⁴, ‖X‖_F², ‖X‖_F⁴ → extended nonnegative (lintegral) expectations; reason: covers every random matrix X, including those with infinite moments, and equals the ordinary expectation whenever it is finite
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 7 (PDF p. 8), Lemma 5

import Mathlib
import Definitions.Def_KoanaKPaths_Main_Estimator

open MeasureTheory ProbabilityTheory

namespace KoanaKPaths.Main

/-- **Lemma 5** (One sketching step; Koana, STOC 2027 submission #953, printed p. 7 / PDF p. 8).
Let `d, t, ℓ` be positive integers, `X` a random real `d × t` matrix and `R ∈ {±1}^{ℓ×d}` a random
sign matrix with mutually independent uniform entries, independent of `X`. Then
`E‖RX‖_F² = ℓ E‖X‖_F²` and `E‖RX‖_F⁴ ≤ ℓ²(1 + 2/ℓ) E‖X‖_F⁴`; the same `R` multiplies all `t`
columns. Expectations are extended nonnegative integrals, so no moment of `X` is assumed finite. -/
theorem one_sketching_step (d t ℓ : ℕ) (hd : 0 < d) (ht : 0 < t) (hℓ : 0 < ℓ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Fin d → Fin t → ℝ) (R : Ω → Fin ℓ → Fin d → Bool)
    (hX : Measurable X) (hR : Measurable R)
    (hRlaw : P.map R = (PMF.uniformOfFintype (Fin ℓ → Fin d → Bool)).toMeasure)
    (hind : IndepFun X R P) :
    ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω))) ∂P =
        (ℓ : ENNReal) * ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω)) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (realFrobSq (signMul (R ω) (X ω)) ^ 2) ∂P ≤
        ENNReal.ofReal ((ℓ : ℝ) ^ 2 * (1 + 2 / (ℓ : ℝ))) *
          ∫⁻ ω, ENNReal.ofReal (realFrobSq (X ω) ^ 2) ∂P := by sorry

end KoanaKPaths.Main
