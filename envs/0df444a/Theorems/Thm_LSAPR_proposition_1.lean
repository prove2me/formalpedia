-- Prove2me | Theorems.Thm_LSAPR_proposition_1
-- name    : LSAPR.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:53.296979+00:00
-- url     : https://prove2.me/theorems/10d3ae6b-1eb3-4012-8b2b-5aa3249566aa
-- title:
--   Proposition 1 — the Lyapunov matrix $Q$ exists, is unique, and makes $\mathrm I-\alpha\bar{\mathbf A}$ a contraction
-- statement:
--   Let $d\ge1$ and let $\bar{\mathbf A}\in\mathbb R^{d\times d}$ be such that $-\bar{\mathbf A}$ is Hurwitz, i.e. every eigenvalue of $\bar{\mathbf A}$ has positive real part. Then there is exactly one symmetric positive definite matrix $Q$ with
--   $$\bar{\mathbf A}^\top Q+Q\bar{\mathbf A}=\mathrm I.$$
--   Moreover, with $a=\|Q\|^{-1}/2$ and $\alpha_\infty=\tfrac12\|\bar{\mathbf A}\|_Q^{-2}\|Q\|^{-1}\wedge\|Q\|$ as in (6), for every $\alpha\in[0,\alpha_\infty]$,
--   $$\|\mathrm I-\alpha\bar{\mathbf A}\|_Q^2\le1-a\alpha,\qquad\alpha a\le\tfrac12.$$
--
--   This contraction property turns the deterministic product $(\mathrm I-\alpha\bar{\mathbf A})^{n}$ into a geometric decay, and it is the source of every constant of the paper.
--
--   Differences from the source:
--   - encoding: the contraction is stated for the unique Q → the clause quantifies over every Q with IsLyapunov Ā Q; reason: the first clause says there is exactly one such Q
--   - encoding: ℝ^d with no lower bound on the dimension stated → the binder 1 ≤ d; reason: the dimension of ℝ^d is a positive integer throughout the paper; at d = 0 the space is {0}, λ_max(Q), λ_min(Q) and ‖Ā‖_Q are undefined and log d (Theorems 1, 2) is −∞, so only undefined cases are excluded
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, Proposition 1, p.4

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- Proposition 1 (Durmus et al. 2021a, Proposition 1), arXiv:2207.04475v2, p.4: if `-Ā` is
Hurwitz, the Lyapunov equation `Āᵀ Q + Q Ā = I` has a unique symmetric positive definite
solution `Q`, and with `a`, `α∞` as in (6), for every `α ∈ [0, α∞]` one has
`‖I - α Ā‖_Q² ≤ 1 - a α` and `α a ≤ 1/2`.

**Formalization Note.** `Matrix.PosDef` includes symmetry. The contraction clause is stated for
every solution `Q`; by uniqueness that is the solution. -/
theorem proposition_1 {d : ℕ} (hd : 1 ≤ d) (Ā : Mat d) (hĀ : EigenRePos Ā) :
    (∃! Q : Mat d, IsLyapunov Ā Q) ∧
      ∀ Q : Mat d, IsLyapunov Ā Q → ∀ α : ℝ, 0 ≤ α → α ≤ alphaInf Ā Q →
        matQNorm Q (1 - α • Ā) ^ 2 ≤ 1 - aQ Q * α ∧ α * aQ Q ≤ 1 / 2 := by sorry

end LSAPR
