-- Prove2me | Theorems.Thm_Monod_exists_countable_dense_subring_of_ne_bot
-- name    : Monod.exists_countable_dense_subring_of_ne_bot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T12:52:58.128014+00:00
-- url     : https://prove2.me/theorems/b2adc007-d206-4ced-9b1a-d396ef31619f
-- title:
--   p. 2 — a subring A ≠ ℤ of ℝ contains a countable dense subring
-- statement:
--   If $A$ is a subring of $\mathbf{R}$ other than $\mathbf{Z}$, there is a subring $A' \subseteq A$ that is countable and dense in $\mathbf{R}$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, proof of Theorem 1

import Mathlib

namespace Monod

theorem exists_countable_dense_subring_of_ne_bot {A : Subring ℝ} (hA : A ≠ ⊥) :
    ∃ A' : Subring ℝ, A' ≤ A ∧ Countable A' ∧ Dense (A' : Set ℝ) := by
  sorry

end Monod
