-- Prove2me | Theorems.Thm_IntervalToDynamic_eq_15
-- name    : IntervalToDynamic.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:01.317906+00:00
-- url     : https://prove2.me/theorems/f0525e09-9dc9-4fe4-a1d5-84c7b748ef20
-- title:
--   Eq. (15) — decomposition of dynamic regret over the pieces
-- statement:
--   Suppose Assumptions 1 and 2 hold for the selected loss class on all rounds. Let $y_t\in\mathcal Y$, $x_t=\Pi_{\mathcal X}[y_t]$, let $h_t$ be the surrogates of Algorithm 1 built from them, and let $u_t\in\mathcal X$. For any partition of $[T]$ into consecutive nonempty pieces $I$ with comparators $z_I\in\mathcal Y$,
--   $$
--   \text{D-Reg}_T(\{u_t\}_{t=1}^T)\le\sum_I\bigl(\text{I-Reg}_I(z_I)+\text{Err}_I(z_I)\bigr),
--   $$
--   with I-Reg and Err evaluated on the surrogates and the decisions $y_t$.
--
--   This is the point at which interval guarantees enter the dynamic regret.
--
--   Differences from the source:
--   - generalization: the pieces I_{j,s} from the partition of Lemma 11 refined by Theorem 6 → any partition of [T] into consecutive nonempty pieces, as a flat list; reason: the printed double sum is one such list
--   - generalization: y_t the decisions of A in the run → any y_t ∈ Y; reason: the run has y_t ∈ Y
--   - generalization: f_t differentiable on the domain, with gradient ∇f_t → any gradient oracle with `HasGradientWithinAt` on the domain; reason: the domain may have empty interior; the gradient of a differentiable loss is such an oracle, so the printed case is included
--   - encoding: X compact convex, with Π_X and X^T presupposing a point → `X.Nonempty` inside `SatisfiesAssumptions`; reason: Π_X and comparators in X need a point; no instance of the paper is excluded
--   - encoding: a comparator z_{j,s} per piece → a function `z`, read at the left end of each piece; reason: pieces have distinct left ends
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, §3.2, Eq. (15), p.10

import Mathlib
import Definitions.Def_IntervalToDynamic_roundLoss
import Definitions.Def_IntervalToDynamic_SatisfiesAssumptions
import Definitions.Def_IntervalToDynamic_IsIntervalPartition
import Definitions.Def_IntervalToDynamic_intervalRegret
import Definitions.Def_IntervalToDynamic_approxError
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs
open ModernOnlineLearning.Dynamic (dynamicRegret pathLength)

namespace IntervalToDynamic

/-- Eq. (15), the regret decomposition. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, §3.2, Eq. (15), p.10.

Let `y_t ∈ Y`, `x_t = Π_X[y_t]`, and let `h_t` be the surrogates built from them as in Algorithm 1.
For any partition of `[T]` into consecutive nonempty pieces `I` and comparators `z_I ∈ Y`,
`D-Reg_T(u) ≤ ∑_I (I-Reg_I(z_I) + Err_I(z_I))`, with `I-Reg_I` and `Err_I` evaluated on `h_t`, `y_t`.

**Formalization Note.** The double sum over `(j, s)` of Eq. (15) is one flat list of pieces, and the
comparator of a piece is `z` at its left end. The partition is any partition, of which the
page's refinement by Theorem 6 is an instance. -/
theorem eq_15 {d : ℕ} (hd : 0 < d) (mode : LossMode) (T : ℕ) (hT : 1 ≤ T) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hAss : ∀ t ∈ Finset.Icc 1 T, SatisfiesAssumptions mode X DX G (f t) (g t))
    (y u : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t ∈ Finset.Icc 1 T, y t ∈ Metric.closedBall 0 DX)
    (hu : ∀ t ∈ Finset.Icc 1 T, u t ∈ X)
    (L : List (ℕ × ℕ)) (hL : IsIntervalPartition T 1 L) (z : ℕ → EuclideanSpace ℝ (Fin d))
    (hz : ∀ p ∈ L, z p.1 ∈ Metric.closedBall 0 DX) :
    dynamicRegret f (fun t => proj X (y t)) u T ≤
      (L.map fun p =>
        intervalRegret (fun t => roundLoss mode X DX G (g t) (y t)) y p.1 p.2 (z p.1) +
        approxError (fun t => roundLoss mode X DX G (g t) (y t)) u p.1 p.2 (z p.1)).sum := by sorry

end IntervalToDynamic
