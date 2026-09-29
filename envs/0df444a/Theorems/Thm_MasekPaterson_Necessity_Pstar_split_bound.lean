-- Prove2me | Theorems.Thm_MasekPaterson_Necessity_Pstar_split_bound
-- name    : MasekPaterson.Necessity.Pstar_split_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:21:09.879846+00:00
-- url     : https://prove2.me/theorems/89123cc5-cfa7-4462-8148-22e15446a2a0
-- title:
--   Lemma 6 — a path to (k+1, k) through the centre diagonal costs at least 5 + (μ_{k+1} + μ_k)π
-- statement:
--   In the §4.1 example, for all natural numbers $k$ and $k'$ with $0 \le k' \le k$,
--
--   $$P^*(0, 0, k') + 5 + P^*(k' + 1, k', k - k') \ge 5 + (\mu_{k+1} + \mu_k)\,\pi.$$
--
--   The left-hand side is the cost of a path that runs along eccentricity $0$ from $(0,0)$ to $(k', k')$, deletes one character (cost $5$), and runs along eccentricity at least $1$ from $(k' + 1, k')$ to $(k + 1, k)$. The lemma says every such path costs at least as much as the path that deletes first and then follows the odd diagonal.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 29, Lemma 6

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Lemma 6: for all `k'` with `0 ≤ k' ≤ k`,
`P*(0, 0, k') + 5 + P*(k' + 1, k', k - k') ≥ 5 + (μ_{k+1} + μ_k) π`. -/
theorem Pstar_split_bound (k k' : ℕ) (hk' : k' ≤ k) :
    5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi
      ≤ exPstar 0 0 k' + 5 + exPstar (k' + 1) k' (k - k') := by sorry

end MasekPaterson.Necessity
