-- Prove2me | Theorems.Thm_LinearOptimization_interior_point_kkt_sufficiency
-- name    : LinearOptimization.interior_point_kkt_sufficiency
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:45:43.044501+00:00
-- url     : https://prove2.me/theorems/a1ce9bfc-8456-4a98-8931-56b8cecaea52
-- title:
--   Sufficiency of the KKT conditions for the barrier problems (points on the central path)
-- statement:
--   **(Lemma 9.5, p. 421)** If $\mathbf{x}^*$, $\mathbf{p}^*$, and $\mathbf{s}^*$ satisfy conditions (9.17) [$A\mathbf{x}^* = \mathbf{b}$, $\mathbf{x}^* \ge \mathbf{0}$, $A'\mathbf{p}^* + \mathbf{s}^* = \mathbf{c}$, $\mathbf{s}^* \ge \mathbf{0}$, $X^*S^*\mathbf{e} = \mu\mathbf{e}$ for a given $\mu > 0$], then they are optimal solutions to problems (9.15) and (9.16), i.e., $\mathbf{x}^* = \mathbf{x}(\mu)$, $\mathbf{p}^* = \mathbf{p}(\mu)$, $\mathbf{s}^* = \mathbf{s}(\mu)$:
--
--   $$B_\mu(\mathbf{x}^*) \le B_\mu(\mathbf{x})$$
--
--   for every $\mathbf{x} > \mathbf{0}$ with $A\mathbf{x} = \mathbf{b}$ (with equality iff $\mathbf{x} = \mathbf{x}^*$, so $\mathbf{x}^*$ is the unique minimizer), and symmetrically $(\mathbf{p}^*, \mathbf{s}^*)$ is optimal for the dual barrier problem (9.16).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Lemma 9.5, p. 421

import Definitions.Def_LinearOptimization_LogBarrier_CentralPath


open Matrix

/-- **Bertsimas & Tsitsiklis, Lemma 9.5 (p. 421).** KKT sufficiency for the barrier problems:
a solution `(x*, p*, s*)` of (9.17) at `μ > 0` has `x*` as the unique
minimizer of `B_μ` over the interior primal feasible set, and `(p*, s*)`
as a maximizer of the dual barrier objective over the interior dual
feasible set. -/

theorem LinearOptimization.interior_point_kkt_sufficiency {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (mu : ℝ) (hmu : 0 < mu)
    (xstar : Fin n → ℝ) (pstar : Fin m → ℝ) (sstar : Fin n → ℝ)
    (hkkt : IsCentralPathPoint A b c mu xstar pstar sstar) :
    (∀ x : Fin n → ℝ, A.mulVec x = b → (∀ j, 0 < x j) →
      logBarrier c mu xstar ≤ logBarrier c mu x ∧
        (logBarrier c mu x = logBarrier c mu xstar → x = xstar)) ∧
    (∀ (p : Fin m → ℝ) (s : Fin n → ℝ), Aᵀ.mulVec p + s = c →
      (∀ j, 0 < s j) →
      dualLogBarrier b mu p s ≤ dualLogBarrier b mu pstar sstar) := by
  sorry
