-- Prove2me | Theorems.Thm_MinSumFPT_isometry_display
-- name    : MinSumFPT.isometry_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:04.802419+00:00
-- url     : https://prove2.me/theorems/f2351571-fe3c-44a8-b026-3487b9bf33e3
-- title:
--   §2.1 — $\|e_x-e_y\|_{W_1}=d(x,y)$ and $\|e_x-\pi\|_{W_1}=\sum_y\pi(y)d(x,y)$
-- statement:
--   Let $d$ be a pseudometric on the finite set $A$ and let $\|\cdot\|_{W_1}$ be the transportation norm on zero-sum vectors of $\mathbb R^A$. Then for all $x,y\in A$,
--
--   $$
--   \|e_x-e_y\|_{W_1}=d(x,y),
--   $$
--
--   and more generally, for every $x\in A$ and every probability vector $\pi$ on $A$ ($\pi\ge0$, $\sum_y\pi(y)=1$),
--
--   $$
--   \|e_x-\pi\|_{W_1}=\sum_{y\in A}\pi(y)\,d(x,y).
--   $$
--
--   The first identity makes $x\mapsto e_x$ an isometric embedding of $(A,d)$ into $W_1(A,d)$. The second computes the distance from a point to a cluster's uniform distribution, which is how $\Delta_C$ and the approximate centers are evaluated.
--
--   Differences from the source:
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
--   - encoding: the norm with unit ball conv{(e_x − e_y)/d(x,y)} → the flow form PerturbedWF.transNorm; reason: equal for a metric; the extension for a pseudometric, where the unit-ball formula divides by 0
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.1, isometry display, p.8

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Delta

namespace MinSumFPT

/-- §2.1, isometry display (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §2.1, p.8): for `x, y ∈ A`,
`‖e_x − e_y‖_{W₁} = d(x, y)`, and for every probability vector `π` on `A`,
`‖e_x − π‖_{W₁} = ∑_{y∈A} π(y) ⋅ d(x, y)`.

**Formalization Note.** `d` is a pseudometric (the paper's semi-metric, footnote 1, p.1);
`‖·‖_{W₁}` is the flow form `PerturbedWF.transNorm d`. -/
theorem isometry_display {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d) :
    (∀ x y : Fin n, PerturbedWF.transNorm d (unitVec x - unitVec y) = d x y) ∧
    ∀ (x : Fin n) (π : Fin n → ℝ), (∀ y, 0 ≤ π y) → ∑ y, π y = 1 →
      PerturbedWF.transNorm d (unitVec x - π) = ∑ y, π y * d x y := by sorry

end MinSumFPT
