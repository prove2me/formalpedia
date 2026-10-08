-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_7
-- name    : NoisyMC.Convex.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:07.094461+00:00
-- url     : https://prove2.me/theorems/19c6fa17-421e-4e55-9b3f-511e735fbce5
-- title:
--   Lemma 7 — uniform injectivity: p⁻¹‖P_Ω(H)‖²_F ≥ ‖H‖²_F/(32κ) on the tangent space of XYᵀ for all (X, Y) obeying (79)
-- statement:
--   Let $M^\star\in\mathbb R^{n\times n}$ have rank $r\ge1$, be $\mu$-incoherent (Definition 1) and have condition number $\kappa$, with balanced factors $X^\star,Y^\star$ (16). Let $\Omega$ follow Bernoulli($p$) sampling (Assumption 1(a)), and suppose $n^2p\ge C\mu rn\log n$ for a sufficiently large constant $C>0$. Then with probability exceeding $1-O(n^{-10})$,
--
--   $$\frac1p\|\mathcal P_\Omega(H)\|_F^2\ge\frac1{32\kappa}\|H\|_F^2\qquad\text{for all }H\in T$$
--
--   holds simultaneously for all $(X,Y)$ with
--
--   $$\max\{\|X-X^\star\|_{2,\infty},\|Y-Y^\star\|_{2,\infty}\}\le\frac c{\kappa\sqrt n}\|X^\star\|,\qquad(79)$$
--
--   where $c>0$ is a sufficiently small constant and $T=\{XA^\top+BY^\top:A,B\in\mathbb R^{n\times r}\}$ is the tangent space of $XY^\top$.
--
--   Unlike classical injectivity results on a single fixed tangent space, this bound is uniform over a neighbourhood of the truth. It therefore applies to tangent spaces that depend on $\Omega$, such as that of the gradient-descent iterates. It is the Condition 2 half of Lemma 4.
--
--   **Formalization Note.** There are $C,c,C_{\rm fail}>0$ and $n_0$ such that for every $n\ge n_0$ and all data, the failure probability is at most $C_{\rm fail}n^{-10}$. $\mu$-incoherence is `MatrixCompletion.A0 S μ`, i.e. $\|U^\star\|_{2,\infty}^2,\|V^\star\|_{2,\infty}^2\le\mu r/n$. $\|X^\star\|$ is the spectral norm of the $n\times r$ matrix $X^\star$.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 31, Lemma 7, (79)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 7 (p. 31). There are constants `C, c, C_fail > 0` and `n₀` such that for every
`n ≥ n₀`, every rank-`r` `µ`-incoherent `M⋆ ∈ ℝ^{n×n}` (SVD `S`, balanced factors `X⋆, Y⋆` of (16),
condition number `κ`), every `0 < p ≤ 1` and every Bernoulli(`p`) sampling pattern
(Assumption 1(a)) with `n² p ≥ C µ r n log n`: with probability at least `1 − C_fail n^{-10}`,
simultaneously for all `(X, Y)` with
`max{‖X − X⋆‖_{2,∞}, ‖Y − Y⋆‖_{2,∞}} ≤ c/(κ√n) ‖X⋆‖` (79),
`p⁻¹ ‖P_Ω(H)‖_F² ≥ (32κ)⁻¹ ‖H‖_F²` for every `H = X Aᵀ + B Yᵀ` in the tangent space of `X Yᵀ`. -/
theorem lemma_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ (μ : ℝ) (Mstar : RealMatrix n n) (S : SVD Mstar r), A0 S μ →
    ∀ p : ℝ, 0 < p → p ≤ 1 →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool),
      SamplingModel P p δ →
      C * μ * r * n * Real.log n ≤ (n : ℝ) ^ 2 * p →
      P {ω | ¬ ∀ X Y : RealMatrix n r,
          max (twoInfNorm (X - Xstar S)) (twoInfNorm (Y - Ystar S)) ≤
            c / (condNum S * Real.sqrt n) * spectralNorm (Xstar S) →
          Condition2 (obsSet δ ω) p (1 / (32 * condNum S)) X Y} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) := by sorry

end NoisyMC.Convex
