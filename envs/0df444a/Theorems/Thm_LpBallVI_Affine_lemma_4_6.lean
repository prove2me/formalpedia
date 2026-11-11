-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_6
-- name    : LpBallVI.Affine.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:54.094297+00:00
-- url     : https://prove2.me/theorems/a761af48-9e7d-41d5-a375-f0647d9900e2
-- title:
--   Lemma 4.6 — Lipschitz, compactly supported, rational piecewise-linear f is uniformly approximated by Σ_j α_j k_λ(a_j t + β_j) for λ near 1
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$, and let $f : \mathbb R \to \mathbb R$ be $L_f$-Lipschitz, compactly supported and rational piecewise-linear. For every $\eta > 0$ there are $m \ge 1$, rationals $\alpha_j, \beta_j$ and $a_j > 0$ ($j \in [m]$) and constants $\kappa, B > 0$ such that $N_{f,\lambda}(t) = \sum_{j=1}^m \alpha_j k_\lambda(a_j t + \beta_j)$ satisfies
--   $$\text{(i)}\ \ \|N_{f,\lambda} - f\|_\infty \le \eta \ \text{ whenever } |\lambda - 1| \le \kappa, \qquad \text{(ii)}\ \ |N_{f,\lambda}(t)| \le B \ \ \forall t \in \mathbb R,\ \lambda > 0.$$
--   Applied to compactly supported versions of the threshold functions, it lets affine VI solutions simulate PureCircuit gates.
--
--   Differences from the source:
--   - encoding: rational piecewise-linear; compactly supported → IsRatPiecewiseLinear (finite rational breakpoint set; affine with rational slope and intercept on each closed interval free of breakpoints in its interior); IsCompactlySupported (Definition 4.5); reason: explicit definitions of the hypotheses
--   - encoding: ‖N_{f,λ} − f‖_∞ ≤ η → |N_{f,λ}(t) − f(t)| ≤ η for every t; reason: sup norm written pointwise
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 25, Lemma 4.6, (23); Definition 4.5

import Mathlib
import Definitions.Def_LpBallVI_Affine_WeightedApprox

namespace LpBallVI.Affine

/-- **Lemma 4.6**, p. 25: for `1 < p < ∞`, `p ≠ 2`, an `L_f`-Lipschitz, compactly supported, rational
piecewise-linear `f : ℝ → ℝ` and `η > 0`, there are `m ≥ 1`, rationals `α_j, β_j`, `a_j > 0` and
`κ, B > 0` such that `N_{f,λ}(t) = ∑_j α_j k_λ(a_j t + β_j)` satisfies (i) `‖N_{f,λ} − f‖_∞ ≤ η`
whenever `|λ − 1| ≤ κ`, and (ii) `|N_{f,λ}(t)| ≤ B` for all `t` and all `λ > 0`. -/
theorem lemma_4_6 (p : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (f : ℝ → ℝ) (Lf : ℝ)
    (hLip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) (hsupp : IsCompactlySupported f)
    (hpl : IsRatPiecewiseLinear f) (η : ℝ) (hη : 0 < η) :
    ∃ (m : ℕ) (α β a : Fin m → ℚ), 1 ≤ m ∧ (∀ j, 0 < a j) ∧
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧
        (∀ lam : ℝ, |lam - 1| ≤ κ → ∀ t : ℝ,
          |weightedApprox p lam (fun j => (α j : ℝ)) (fun j => (a j : ℝ)) (fun j => (β j : ℝ)) t
            - f t| ≤ η) ∧
        (∀ lam : ℝ, 0 < lam → ∀ t : ℝ,
          |weightedApprox p lam (fun j => (α j : ℝ)) (fun j => (a j : ℝ)) (fun j => (β j : ℝ)) t|
            ≤ B) := by sorry

end LpBallVI.Affine
