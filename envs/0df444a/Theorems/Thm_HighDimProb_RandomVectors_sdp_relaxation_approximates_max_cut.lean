-- Prove2me | Theorems.Thm_HighDimProb_RandomVectors_sdp_relaxation_approximates_max_cut
-- name    : HighDimProb.RandomVectors.sdp_relaxation_approximates_max_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T06:45:36.694786+00:00
-- url     : https://prove2.me/theorems/abc21244-c86c-48b2-8f84-cbd327740657
-- title:
--   Theorem 3.5.6 — SDP relaxation guarantees for symmetric PSD matrices
-- statement:
--   This is **Theorem 3.5.6**, the chapter's headline application of Grothendieck's inequality:
--   the tractable semidefinite relaxation $\mathrm{SDP}(A)$ (the companion definition
--   `SdpRelaxationValue`) always approximates the intractable integer optimum $\mathrm{INT}(A)$
--   (the companion definition `IntegerCutValue`) to within an absolute constant factor,
--   whenever $A$ is symmetric and positive-semidefinite.
--
--   There is an absolute constant $K$, $0 < K \le 288$ (the constant of Grothendieck's
--   inequality, Theorem 3.5.1), such that the following holds. Let $n \in \mathbb N$ and let $A$
--   be an $n \times n$ real, symmetric, positive-semidefinite matrix. Then
--
--   $$
--   \mathrm{INT}(A) \;\le\; \mathrm{SDP}(A) \;\le\; 2K \cdot \mathrm{INT}(A).
--   $$
--
--   The lower bound is immediate (every feasible sign vector for (3.20) is also feasible for
--   (3.21), embedded as a unit vector along one coordinate axis); the upper bound is the
--   genuinely nontrivial direction, obtained from the symmetric-matrix form of Grothendieck's
--   inequality (Exercise 3.5.3) applied to $A$'s positive-semidefinite structure. Together, the
--   two bounds certify that solving the tractable convex program (3.21) never overestimates the
--   hard combinatorial optimum by more than a constant factor — the guarantee that makes
--   semidefinite relaxation a useful algorithmic tool for problems like maximum cut.
--
--   **Formalization Note** Positive-semidefiniteness is Mathlib's `Matrix.PosSemidef`, which
--   bundles the Hermitian (for a real matrix, symmetric) condition together with the
--   nonnegative-quadratic-form condition, so no separate symmetry hypothesis is needed. $K$ is
--   existentially quantified ahead of the matrix $A$ and its dimension, using this chunk's
--   $K \le 288$ bound (matching the goal theorem, `grothendieck_inequality`) rather than the
--   book's sharper $K \le 1.783$; the two draft items are not linked by a Lean import (drafts in
--   a mission cannot import each other's unproved statements), but assert the same numerical
--   bound.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 3.5.6, p. 65 (PDF p. 73)

import Mathlib
import Definitions.Def_HighDimProb_RandomVectors_IntegerCutValue
import Definitions.Def_HighDimProb_RandomVectors_SdpRelaxationValue

namespace HighDimProb.RandomVectors

/-- **Theorem 3.5.6**, Vershynin, *High-Dimensional Probability* (2018), p. 65.

Consider an `n × n` symmetric, positive-semidefinite matrix `A`. Let `INT(A)` denote the
maximum in the integer optimization problem (3.20) and `SDP(A)` denote the maximum in the
semidefinite problem (3.21). Then

`INT(A) ≤ SDP(A) ≤ 2K · INT(A)`

where `K ≤ 288` is the constant from Grothendieck's inequality (Theorem 3.5.1, this chunk's
`K ≤ 288` first-pass bound). -/
theorem sdp_relaxation_approximates_max_cut :
    ∃ K : ℝ, 0 < K ∧ K ≤ 288 ∧
      ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), A.PosSemidef →
        integerCutValue A ≤ sdpRelaxationValue A ∧
        sdpRelaxationValue A ≤ 2 * K * integerCutValue A := by sorry

end HighDimProb.RandomVectors
