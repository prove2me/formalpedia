-- Prove2me | Theorems.Thm_LassoDantzig_Oracle_eq_B4_noise_event
-- name    : LassoDantzig.Oracle.eq_B4_noise_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:08:24.776446+00:00
-- url     : https://prove2.me/theorems/c8a29cc7-1bc9-4017-88f8-0dde1b36a7ec
-- title:
--   Eq. (B.4) — the Gaussian noise event has probability at least $1-M^{1-A^2/8}$
-- statement:
--   Let $n\ge1$, $M\ge2$, let $X\in\mathbb R^{n\times M}$ have nonzero column norms $\|f_j\|_n$, and let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma>0$. Put $r=A\sigma\sqrt{\log M/n}$ with $A>2\sqrt2$, $V_j=n^{-1}\sum_{i=1}^n X_{ij}W_i$ and
--   $$\mathcal A=\bigcap_{j=1}^M\{2|V_j|\le r\|f_j\|_n\}.$$
--   Then $\mathcal A$ is an event (measurable) and
--   $$P(\mathcal A^c)\le M^{1-A^2/8}.$$
--
--   This is the only probabilistic ingredient of Lemma B.1 and Theorem 6.1: every other step of their proofs is deterministic on $\mathcal A$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 21, Appendix B, proof of Lemma B.1, Eq. (B.4)

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **(B.4)** (Bickel–Ritov–Tsybakov, p. 21, proof of Lemma B.1). Let `W_1, …, W_n` be independent
`N(0, σ²)`, `σ > 0`, and `r = Aσ√(log M / n)` with `A > 2√2`. The event
`𝒜 = ⋂_j {2|V_j| ≤ r‖f_j‖_n}`, `V_j = n⁻¹ ∑ᵢ f_j(Z_i) W_i`, is measurable and
`P(𝒜ᶜ) ≤ M^{1 − A²/8}`. -/
theorem eq_B4_noise_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    MeasurableSet (noiseEvent X W (tuning n M A σ)) ∧
      P (noiseEvent X W (tuning n M A σ))ᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by sorry

end LassoDantzig.Oracle
