-- Prove2me | Theorems.Thm_MasekPaterson_Necessity_Pstar_lower_bound
-- name    : MasekPaterson.Necessity.Pstar_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:20:40.521683+00:00
-- url     : https://prove2.me/theorems/821d78d3-b7ef-4daa-9245-e48ea7278091
-- title:
--   Lemma 5 — lower bounds for P*(i, j, k) on even and odd diagonals
-- statement:
--   In the §4.1 example, with $\mu$ and $P^*$ as defined there, for all natural numbers $i, j, k$:
--
--   1. if $i - j$ is even, then $$P^*(i, j, k) \ge k - \mu_{i+k} + \mu_i;$$
--   2. if $i - j$ is odd, then $$P^*(i, j, k) \ge (\mu_{i+k} - \mu_i + \mu_{j+k} - \mu_j)\,\pi.$$
--
--   The right-hand sides are the costs of the straight diagonal paths when the $c$'s line up: on an even diagonal each step costs $1$ except a $c$-for-$c$ replacement, which is free; on an odd diagonal each $c$ met costs $\pi$ and every other step is free. The lemma says that no path staying at eccentricity at least $|i - j|$ does better.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 28, Lemma 5

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 5: `P*(i, j, k) ≥ k - μ_{i+k} + μ_i` if `i - j` is even, and
`P*(i, j, k) ≥ (μ_{i+k} - μ_i + μ_{j+k} - μ_j) π` if `i - j` is odd. -/
theorem Pstar_lower_bound (i j k : ℕ) :
    (Even ((i : ℤ) - j) →
      (k : ℝ) - (mu (i + k) : ℝ) + (mu i : ℝ) ≤ exPstar i j k) ∧
    (Odd ((i : ℤ) - j) →
      ((mu (i + k) : ℝ) - (mu i : ℝ) + (mu (j + k) : ℝ) - (mu j : ℝ)) * Real.pi
        ≤ exPstar i j k) := by sorry

end MasekPaterson.Necessity
