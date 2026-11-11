-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_C_2
-- name    : MarginMaxima.Critical.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:01:52.109747+00:00
-- url     : https://prove2.me/theorems/4c6ce10f-01b3-4ca8-ab7b-6967b9cdfd81
-- title:
--   Lemma C.2 — packing with a tolerated fraction: $|U|\le 2\exp(4\rho^2\ln(8/\delta)/t^2)$
-- statement:
--   Let $x_1,\dots,x_m$ lie in the unit ball of $\mathbb R^D$, and let $t,\rho>0$, $\delta\in(0,1]$. If $U$ lies in the ball of radius $\rho$ and for distinct $u,v\in U$ more than $\delta m$ indices $i$ have $|\langle u-v,x_i\rangle|>t$, then
--   $$|U|\le 2\exp\!\big(4\rho^2\ln(8/\delta)/t^2\big).$$
--   This packing bound is the covering step in the proof of Theorem C.1.
--
--   Differences from the source:
--   - encoding: |U| ≤ 2exp(…) for a set U → U : Set (EuclideanSpace ℝ (Fin D)), conclusion U.Finite ∧ U.ncard ≤ 2exp(…); reason: the bound asserts in particular that U is finite; ncard alone would be 0 for an infinite U
--   - encoding: more than δm indices i have |⟨u − v, x_i⟩| > t; the ball of radius ρ → δ·m < card of the filter of Fin m; Metric.closedBall 0 ρ; reason: literal transcription; the ball is closed as everywhere in the paper
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 31, Lemma C.2

import Mathlib

namespace MarginMaxima.Critical

theorem lemma_C_2 (D m : ℕ) (x : Fin m → EuclideanSpace ℝ (Fin D)) (hx : ∀ i, ‖x i‖ ≤ 1)
    (t ρ δ : ℝ) (ht : 0 < t) (hρ : 0 < ρ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (U : Set (EuclideanSpace ℝ (Fin D))) (hU : U ⊆ Metric.closedBall 0 ρ)
    (hsep : ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      δ * m < ((Finset.univ.filter fun i => t < |inner ℝ (u - v) (x i)|).card : ℝ)) :
    U.Finite ∧ (U.ncard : ℝ) ≤ 2 * Real.exp (4 * ρ ^ 2 * Real.log (8 / δ) / t ^ 2) := by sorry

end MarginMaxima.Critical
