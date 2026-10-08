-- Prove2me | Theorems.Thm_MinRankRecovery_RandomRIP_lemma_4_3
-- name    : MinRankRecovery.RandomRIP.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:16.042189+00:00
-- url     : https://prove2.me/theorems/d8476757-bb34-4b9b-900b-94e41a999ab0
-- title:
--   Lemma 4.3 — a nearly isometric map is a δ-isometry on a fixed d-dimensional subspace w.h.p.
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a nearly isometric random linear map and let $U\subseteq\mathbb R^{m\times n}$ be a fixed subspace of dimension $d=\dim U\le p$. Then for every $0<\delta<1$ the event
--   $$(1-\delta)\|X\|_F\le\|\mathcal A(X)\|\le(1+\delta)\|X\|_F\qquad\text{for all }X\in U$$
--   holds with probability at least
--   $$1-2\Big(\frac{12}{\delta}\Big)^{d}\exp\Big(-\frac p2\Big(\frac{\delta^2}{8}-\frac{\delta^3}{24}\Big)\Big).$$
--
--   The quantifier over $X\in U$ is inside the event: with the stated probability the map is simultaneously a near-isometry on the whole subspace. This is the step that turns the single-matrix concentration of the definition into a statement about a subspace.
--
--   **Formalization Note** The event need not be measurable, so the statement bounds the (outer) probability of its complement — some $X\in U$ violates the two-sided inequality — by $2(12/\delta)^d\exp(-\frac p2(\delta^2/8-\delta^3/24))$. For a measurable event this is the printed bound.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Lemma 4.3, (4.8)–(4.9), p. 16

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst
import Definitions.Def_MinRankRecovery_RandomRIP_NearlyIsometric

open HighDimStat.MatrixRank MeasureTheory

namespace MinRankRecovery.RandomRIP

/-- Lemma 4.3, p. 16: a nearly isometric random map is, with probability at least
`1 − 2(12/δ)^d exp(−(p/2)(δ²/8 − δ³/24))`, a `δ`-isometry on all of a fixed subspace `U` of
`m × n` matrices with `d = dim U ≤ p`. Stated in complement form: the (outer) probability that
some `X ∈ U` violates (4.8) is at most `2(12/δ)^d exp(−(p/2)(δ²/8 − δ³/24))`. -/
theorem lemma_4_3 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m n p : ℕ} (Xs : Ω → Fin p → Matrix (Fin m) (Fin n) ℝ) (hA : IsNearlyIsometric μ Xs)
    (U : Submodule ℝ (Matrix (Fin m) (Fin n) ℝ)) (hd : Module.finrank ℝ U ≤ p)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | ∃ X ∈ U, ¬ ((1 - δ) * frobeniusNorm X ≤ MinRankRecovery.Recovery.measNorm (Xs ω) X ∧
        MinRankRecovery.Recovery.measNorm (Xs ω) X ≤ (1 + δ) * frobeniusNorm X)} ≤
      ENNReal.ofReal (2 * (12 / δ) ^ (Module.finrank ℝ U) *
        Real.exp (-((p : ℝ) / 2 * (δ ^ 2 / 8 - δ ^ 3 / 24)))) := by sorry

end MinRankRecovery.RandomRIP
