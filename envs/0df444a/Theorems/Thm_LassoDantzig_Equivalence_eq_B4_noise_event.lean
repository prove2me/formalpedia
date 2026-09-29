-- Prove2me | Theorems.Thm_LassoDantzig_Equivalence_eq_B4_noise_event
-- name    : LassoDantzig.Equivalence.eq_B4_noise_event
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:52:51.36317+00:00
-- url     : https://prove2.me/theorems/e35e706a-86f5-4286-8de6-88051e3b01bb
-- title:
--   Appendix B, Eq. (B.4) — the noise event $\mathcal A$ has probability at least $1-M^{1-A^2/8}$
-- statement:
--   Let $n\ge1$, $M\ge2$, and let $X\in\mathbb R^{n\times M}$ have column empirical norms $\|f_j\|_n\ne0$. Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma>0$ on a probability space $(\Omega,\mathbb P)$, and set
--   $$
--   V_j=\frac1n\sum_{i=1}^nX_{ij}W_i,\qquad r=A\sigma\sqrt{\frac{\log M}{n}},\qquad \mathcal A=\bigcap_{j=1}^M\{2|V_j|\le r\|f_j\|_n\},
--   $$
--   with $A>0$ and $\log$ the natural logarithm. Then
--   $$
--   \mathbb P\{\mathcal A^c\}\le M^{1-A^2/8}.
--   $$
--
--   This is the probabilistic input of Lemma B.1 and of Theorems 5.1 and 5.2: all the deterministic comparisons of the Lasso and the Dantzig selector hold on $\mathcal A$.
--
--   **Formalization Note** The paper states (B.4) within the proof of Lemma B.1, where $A>2\sqrt2$; the bound holds, and is stated here, for every $A>0$ (for $A\le2\sqrt2$ its right-hand side is at least $1$). The law of $W_i$ is Mathlib's `gaussianReal 0 σ²`; $W_i$ is assumed measurable (so that its image measure is its law) and the family is mutually independent. The probability is an element of $[0,\infty]$ and the bound is `ENNReal.ofReal` of $M^{1-A^2/8}$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 21, Appendix B, proof of Lemma B.1, Eq. (B.4)

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Equivalence

/-- (B.4): the complement of the noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r‖fⱼ‖_n}` has probability at most
`M^{1 − A²/8}` when `r = Aσ√(log M / n)`. -/
theorem eq_B4_noise_event {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEventHalf X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by sorry

end LassoDantzig.Equivalence
