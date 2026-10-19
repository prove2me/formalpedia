-- Prove2me | Theorems.Thm_LargeBSP_Homog_profit_le_sup_normalized
-- name    : LargeBSP.Homog.profit_le_sup_normalized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:47.898814+00:00
-- url     : https://prove2.me/theorems/2c5df297-14ce-481c-8560-29904cfd4d1a
-- title:
--   Proof of Theorem 1, p. A1 — π(p)/N ≤ sup_{t∈[0,1]} V̄_N(t) − c̄_N(t) for every BSP menu
-- statement:
--   Let $c = (c_n)$ be marginal costs and $x = (x_n)$ a realization of the customer's valuations, $N \ge 1$, and let $p$ be any BSP menu (prices in $\mathbb R_+ \cup \{\infty\}$). Writing $\bar\pi(p) = \pi(p)/N$ for the normalized realized profit, there is $t \in [0,1]$ with
--   $$\bar\pi(p) \le \bar V_N(t) - \bar c_N(t).$$
--   Equivalently $\bar\pi(p) \le \sup_{t \in [0,1]} \bar V_N(t) - \bar c_N(t)$.
--
--   The bound holds realization by realization and is the upper half of the proof of Theorem 1: the firm can never extract more than the value of the purchased bundle minus its cost.
--
--   **Formalization Note** The supremum on the page ranges over finitely many values ($\lfloor Nt \rfloor \in \{0, \dots, N\}$), so it is attained; the Lean statement asserts the existence of a maximizing $t$, which is equivalent and avoids a real supremum. No expectation is involved.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 1 (Appendix A.1), p. A1, first sentence

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

namespace LargeBSP.Homog

/-- Proof of Theorem 1, first sentence, p. A1: for every BSP menu, the normalized realized profit
`π̄(p) = π(p)/N` is at most `sup_{t ∈ [0,1]} V̄_N(t) − c̄_N(t)` (the supremum is over finitely many
values and is attained, hence the `∃`). Pathwise, for every valuation profile `x`. -/
theorem profit_le_sup_normalized (c x : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (p : Menu) (hp : IsBSPMenu p) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, profit c x N p / N ≤ Vbar x N t - cbar c x N t := by sorry

end LargeBSP.Homog
