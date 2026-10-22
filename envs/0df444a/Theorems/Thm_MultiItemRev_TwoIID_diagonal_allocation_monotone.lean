-- Prove2me | Theorems.Thm_MultiItemRev_TwoIID_diagonal_allocation_monotone
-- name    : MultiItemRev.TwoIID.diagonal_allocation_monotone
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-15T12:03:43.240168+00:00
-- url     : https://prove2.me/theorems/00976fee-18fb-4ac0-975b-08d522b76350
-- title:
--   B1 — diagonal allocation of a symmetric IC mechanism is monotone and [0,1]-valued
-- statement:
--   B1 — diagonal-allocation monotonicity (Hart–Nisan, *Approximate Revenue
--   Maximization with Multiple Items*, arXiv:1204.1846v3, pp. 32–33, proof of
--   Theorem B, Eq. (12) setup).
--
--   For a symmetric incentive-compatible mechanism M for two goods, the
--   diagonal allocation t ↦ q(t, t)_0 — the allocation of good 0 when both
--   reported values equal t — is monotone nondecreasing and takes values in
--   [0, 1].
--
--   This is the missing bridge node in the Theorem B chain: display_12 bounds a
--   symmetric mechanism's revenue by an analytic expression in its diagonal
--   allocation, and rhs12_le bounds that analytic expression for any monotone
--   [0, 1]-valued phi. Setting phi := fun t => M.q (diag t) 0, both of
--   rhs12_le's hypotheses follow from this node.
--
--   Proof idea: two IC comparisons (true type (t, t) reporting (t', t') and
--   vice versa) cancel the payments and give
--   (t − t') · (Q(t) − Q(t')) ≥ 0 for the total diagonal allocation
--   Q(t) = q(t, t)_0 + q(t, t)_1. Symmetry gives q(t, t)_0 = q(t, t)_1 (the
--   swap fixes the diagonal), so Q(t) = 2 · q(t, t)_0 and the coordinate-0
--   allocation is monotone. The [0, 1] bounds are feasibility. Symmetry is
--   genuinely needed: IC alone yields monotonicity of the sum Q, not of
--   coordinate 0 alone.
--
--   Only the minimal hypotheses are assumed (feasibility + IC + symmetry);
--   individual rationality, no-positive-transfer, and measurability are not
--   used. display_12 (live, Open) is NOT re-published here — this is B1 only.
-- source:
--   Hart–Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 32–33, proof of Theorem B (diagonal allocation of a symmetric mechanism; Eq. (12) setup)

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

/-- B1: diagonal-allocation monotonicity (Hart–Nisan, arXiv:1204.1846v3,
pp. 32–33, proof of Theorem B, Eq. (12) setup).

For a symmetric incentive-compatible mechanism, the diagonal allocation
`t ↦ M.q (diag t) 0` — the allocation of good 0 when both reported values
are `t` — is monotone and `[0,1]`-valued. This is the bridge that lets the
diagonal allocation feed `φ` into `rhs12_le` via `display_12`: set
`φ := fun t => M.q (diag t) 0` and both of `rhs12_le`'s hypotheses
(`Monotone φ`, `0 ≤ φ t ∧ φ t ≤ 1`) follow from this node.

Proof idea: two IC comparisons — true type `(t,t)` reporting `(t′,t′)`
and vice versa — cancel the payments and give
`(t − t′) · (Q(t) − Q(t′)) ≥ 0` for the total diagonal allocation
`Q(t) = q(t,t) 0 + q(t,t) 1`. Symmetry gives `q(t,t) 0 = q(t,t) 1`
(`swap2` fixes the diagonal), so `Q(t) = 2 · q(t,t) 0` and the
coordinate-0 allocation is monotone. The `[0,1]` bounds are feasibility.
Symmetry is genuinely needed: IC alone yields monotonicity of the sum `Q`,
not of coordinate 0 alone. -/
theorem diagonal_allocation_monotone
    (M : MultiItemRev.Decomp.Mechanism (Fin 2))
    (hFeas : MultiItemRev.Decomp.IsFeasible M)
    (hIC : MultiItemRev.Decomp.IsIC M)
    (hSym : IsSymmetric M) :
    Monotone (fun t => M.q (diag t) 0) ∧
      ∀ t, 0 ≤ M.q (diag t) 0 ∧ M.q (diag t) 0 ≤ 1 := by sorry

end MultiItemRev.TwoIID
