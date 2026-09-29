-- Prove2me | Theorems.Thm_LassoDantzig_Lasso_eq_B4_noise_event
-- name    : LassoDantzig.Lasso.eq_B4_noise_event
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:18:11.627441+00:00
-- url     : https://prove2.me/theorems/4febfe06-1df3-482e-aa74-a24a30c00401
-- title:
--   Appendix B, (B.4) — the noise event $\mathcal A$ fails with probability at most $M^{1-A^2/8}$
-- statement:
--   Let $n\ge1$, $M\ge2$, and let $X\in\mathbb R^{n\times M}$ have unit diagonal Gram matrix, $\frac1n\sum_iX_{ij}^2=1$ for all $j$. Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables with $\sigma>0$, put $V_j=\frac1n\sum_{i=1}^nX_{ij}W_i$, and let $A>0$ and
--   $$
--   r=A\sigma\sqrt{\frac{\log M}{n}} .
--   $$
--   Then the noise event $\mathcal A=\bigcap_{j=1}^M\{2|V_j|\le r\}$ satisfies
--   $$
--   \mathbb P\{\mathcal A^c\}\le M^{1-A^2/8}.
--   $$
--
--   This is the probabilistic input of Theorem 7.2: all the deterministic consequences of the Lasso's optimality are derived on $\mathcal A$.
--
--   **Formalization Note** The paper states (B.4) for general column norms with $r_{n,j}=r\|f_j\|_n$; under the unit diagonal of Section 7, $r_{n,j}=r$. The bound is stated for every $A>0$; the paper uses it with $A>2\sqrt2$, where $M^{1-A^2/8}<1$. $\log$ is the natural logarithm. The probability of the (measurable) complement is bounded in $[0,\infty]$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 21, Appendix B, Eq. (B.4) (proof of Lemma B.1)

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

/-- (B.4), p. 21: under the unit diagonal of Section 7, the complement of the noise event
`𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r}`, `Vⱼ = (1/n) ∑ᵢ X_{ij} Wᵢ`, has probability at most `M^{1 − A²/8}` when
`r = Aσ√(log M / n)`. -/
theorem eq_B4_noise_event {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEventHalf X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by sorry

end LassoDantzig.Lasso
