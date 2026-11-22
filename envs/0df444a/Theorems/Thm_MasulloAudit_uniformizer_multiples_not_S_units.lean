-- Prove2me | Theorems.Thm_MasulloAudit_uniformizer_multiples_not_S_units
-- name    : MasulloAudit.uniformizer_multiples_not_S_units
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:51:08.963988+00:00
-- url     : https://prove2.me/theorems/b528242a-7845-4380-b400-50879c819eb8
-- title:
--   Infinitely many rationals of $p$-adic valuation $1$ are not $S'$-units, for any finite $S'$
-- statement:
--   Let $p$ be a prime and $S'$ any finite set of natural numbers. Then the set of nonzero rationals $\xi$ with
--
--   $$
--   v_p(\xi)=1\qquad\text{and}\qquad v_q(\xi)\ne0\ \text{for some prime } q\notin S'
--   $$
--
--   is infinite. Infinitely many $\xi$ of $p$-adic valuation $1$ are therefore **not** $S'$-units, however large the finite set $S'$ is.
--
--   This contradicts the literal wording of a step in the proof of Theorem 11.3.2.1 of Masullo's draft (p. 495), specialized to $F=\mathbf Q$. There the set $\Xi_k$ of $\xi\in F^\times$ "mapping to a uniformizer" at a place of $P_{k+1}-P_k$ is asserted to lie in $\mathrm{GL}_1(\mathbf A_{F,S'})\times\prod_{v\notin S'}\mathcal O_v^\times$ "for $S'$ large enough", with a single $S'$ fixed in terms of $k$. The elements $\xi=pq$, with $q$ a prime outside $S'$, show that no fixed finite $S'$ works for $\Xi_k$ as defined there, unless further restrictions that the draft does not state exclude them.
--
--   **Formalization Note.** Valuations are Mathlib's `padicValRat`. $S'$ is an arbitrary `Finset ℕ` and need not contain $p$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, proof of Theorem 11.3.2.1, p. 495.

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Set.Finite.Basic

namespace MasulloAudit

/-- For every prime `p` and every finite set `S'` of primes, there are infinitely many
`ξ ∈ ℚ^×` with `v_p(ξ) = 1` that are not `S'`-units (some prime `q ∉ S'` has `v_q(ξ) ≠ 0`).
So the set Ξ_k in the proof of Masullo Thm 11.3.2.1 cannot consist of `S'`-units for a
single finite `S'`. -/
theorem uniformizer_multiples_not_S_units (p : ℕ) [hp : Fact p.Prime] (S' : Finset ℕ) :
    {ξ : ℚ | ξ ≠ 0 ∧ padicValRat p ξ = 1 ∧
      ∃ q : ℕ, q.Prime ∧ q ∉ S' ∧ padicValRat q ξ ≠ 0}.Infinite := by sorry

end MasulloAudit
