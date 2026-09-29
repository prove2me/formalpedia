-- Prove2me | Theorems.Thm_LassoDantzig_Dantzig_noise_event_B
-- name    : LassoDantzig.Dantzig.noise_event_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:12:46.801476+00:00
-- url     : https://prove2.me/theorems/20099ded-b7aa-4221-8d3c-74762b47ffdb
-- title:
--   Proof of Lemma B.3 — the noise event $\mathcal B$ has probability at least $1-M^{1-A^2/2}$
-- statement:
--   Let $n\ge1$, $M\ge2$, and let $X\in\mathbb R^{n\times M}$ have column empirical norms $\|f_j\|_n=(\frac1n\sum_iX_{ij}^2)^{1/2}\neq0$. Let $W_1,\dots,W_n$ be independent $\mathcal N(0,\sigma^2)$ random variables on a probability space $(\Omega,\mathbb P)$, $\sigma>0$, put $V_j=\frac1n\sum_{i=1}^nX_{ij}W_i$, and for $A>0$ let
--
--   $$
--   r=A\sigma\sqrt{\frac{\log M}{n}} .
--   $$
--
--   Then the event $\mathcal B=\bigcap_{j=1}^M\{|V_j|\le r\|f_j\|_n\}$ satisfies
--
--   $$
--   \mathbb P\{\mathcal B^c\}\le M^{1-A^2/2}.
--   $$
--
--   On $\mathcal B$ the true regression vector satisfies the Dantzig constraint; this is the only probabilistic ingredient of the Dantzig selector's rates of convergence (Theorem 7.1). The bound is informative when $A>\sqrt2$.
--
--   **Formalization Note** $\log$ is the natural logarithm. The noise is `W : Fin n → Ω → ℝ` with measurable, mutually independent coordinates of law `gaussianReal 0 σ²`. The statement holds for every $A>0$; the paper applies it with $A>\sqrt2$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 23, proof of Lemma B.3 (event ℬ, 'Analogously to (B.4), P{ℬᶜ} ≤ M^{1−A²/2}')

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Dantzig

/-- Proof of Lemma B.3 (p. 23): with `r = Aσ√(log M / n)`, the complement of the noise event
`ℬ = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n}`, `Vⱼ = (1/n) ∑ᵢ X i j Wᵢ`, has probability at most `M^{1 − A²/2}`
when the `Wᵢ` are independent `N(0, σ²)`. -/
theorem noise_event_B {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEvent X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 2)) := by sorry

end LassoDantzig.Dantzig
