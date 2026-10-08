-- Prove2me | Theorems.Thm_KelsoCrawford_NoCore_example_has_no_core
-- name    : KelsoCrawford.NoCore.example_has_no_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:16.991022+00:00
-- url     : https://prove2.me/theorems/ce78c84d-fe4d-4855-920a-f469b820e72c
-- title:
--   Section 6, p. 1503 — without (GS), the market with firms j, k and three workers has no core allocation
-- statement:
--   Consider the market of the example of Section 6: three workers $1, 2, 3$, two firms $j$ and $k$ with technologies
--
--   | $C$ | $\emptyset$ | $\{1\}$ | $\{2\}$ | $\{3\}$ | $\{1,2\}$ | $\{1,3\}$ | $\{2,3\}$ | $\{1,2,3\}$ |
--   |---|---|---|---|---|---|---|---|---|
--   | $y^j(C)$ | $0$ | $4$ | $4$ | $4\tfrac14$ | $7\tfrac12$ | $7$ | $7$ | $9$ |
--   | $y^k(C)$ | $0$ | $4\tfrac14$ | $4$ | $4$ | $7$ | $7$ | $7\tfrac12$ | $9$ |
--
--   reservation salaries $\sigma_{ij} = \sigma_{ik} = 0$ and utilities $u^i(j; s) = u^i(k; s) = s$. When salaries can vary continuously, this market has no core allocation: there is no assignment of the workers to the firms together with salaries $s_{if(i)}$ such that
--   $$s_{if(i)} \ge 0, \qquad \pi^j(C^j; s^j) \ge 0, \qquad \pi^k(C^k; s^k) \ge 0,$$
--   and no firm together with a set of workers can, with real salaries, make every member of the coalition strictly better off.
--
--   The firms' technologies satisfy (MP) and (NFL) and are subadditive, but violate (GS). The example shows that the gross-substitutes assumption cannot simply be dropped from the paper's existence theorems: without it, the core of a two-sided job-matching market can be empty.
--
--   **Formalization Note** "Core allocation" is D3 with real salaries (`anySalary`): an individually rational allocation that no firm–set-of-workers coalition can strictly improve upon. Every worker is assigned to a firm, as in D1. The paper adds "and thus no competitive equilibrium"; that consequence rests on the core–competitive-equilibrium equivalence of p. 1487 and is not part of this statement.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1503–1504, Section 6, the example with firms j and k

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Model
import Definitions.Def_KelsoCrawford_NoCore_Example

namespace KelsoCrawford.NoCore

theorem example_has_no_core :
    ¬ ∃ A : Allocation (Fin 3) (Fin 2), noCoreMarket.IsCore KelsoCrawford.ContinuousCore.anySalary A := by sorry

end KelsoCrawford.NoCore
