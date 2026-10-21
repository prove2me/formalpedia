-- Prove2me | Theorems.Thm_OffGridStorage_TechChoice_theorem_2
-- name    : OffGridStorage.TechChoice.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:02.241206+00:00
-- url     : https://prove2.me/theorems/00078016-2247-4111-9d66-8e1f2c7c9e8d
-- title:
--   Theorem 2, p. 12 — technology A is preferred to B iff c_K^A/e^A < c_K^B/e^B; storage is profitable iff c_K/e < g − √(2c_Q g)
-- statement:
--   Consider the tracking model of an off-grid utility with $T\ge 1$ periods, day and night demands $D_H,D_L>0$, generation cost $c_Q>0$ and backup cost $g>2c_Q$. A storage technology is a pair $(e,c_K)$ with efficiency $0<e\le 1$ and cost $c_K\ge 0$.
--
--   1. **Comparison of technologies.** For all admissible technologies $A=(e^A,c_K^A)$ and $B=(e^B,c_K^B)$, $A$ is preferred to $B$ in the sense of Definition 1 if and only if
--   $$\frac{c_K^A}{e^A}<\frac{c_K^B}{e^B}.$$
--   2. **Profitability.** A given technology $(e,c_K)$ can profitably be invested in, i.e. the optimal storage investment of the tracking model is positive, if and only if
--   $$\frac{c_K}{e}<g-\sqrt{2c_Qg}.$$
--
--   Here "preferred" means that the set $\Gamma^A$ of market parameters $(c_Q,D_H,D_L,g)$ at which positive storage is optimal under $A$ strictly contains $\Gamma^B$, and "the optimal storage investment is positive" means that an optimal tracking plan exists and every optimal tracking plan has positive storage. The theorem shows that the storage-cost-to-efficiency ratio $c_K/e$ alone ranks technologies and decides their profitability.
--
--   **Formalization Note** The superset in Definition 1 is read as proper; with a non-strict superset, equal ratios would make each technology preferred to the other and the "only if" direction of part 1 would fail. Part 1 holds for every fixed $T\ge 1$; $\Gamma$ ranges over tuples satisfying the market part of the standing assumptions.
-- source:
--   Kaps, Marinesi & Netessine, When Should the Off-grid Sun Shine at Night?, SSRN 3761397 (version of May 11, 2023), p. 12, Theorem 2 (with Definition 1, p. 11); proof Appendix A.2, p. 37

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

namespace OffGridStorage.TechChoice

/-- Theorem 2, p. 12. (a) For every number of periods `T ≥ 1` and admissible technologies `A`,
`B`, `A` is preferred to `B` (Definition 1) iff `c_K^A/e^A < c_K^B/e^B`. (b) Under the standing
assumptions, the optimal tracking storage investment is positive iff `c_K/e < g - √(2 c_Q g)`. -/
theorem theorem_2 :
    (∀ T : ℕ, 1 ≤ T → ∀ A B : Tech, ValidTech A → ValidTech B →
      (Preferred T A B ↔ A.cK / A.e < B.cK / B.e)) ∧
    (∀ p : Params, Standing p →
      (OptimalStoragePos p ↔ p.cK / p.e < p.g - Real.sqrt (2 * p.cQ * p.g))) := by sorry

end OffGridStorage.TechChoice
