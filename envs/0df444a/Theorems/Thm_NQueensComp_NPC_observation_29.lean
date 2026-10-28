-- Prove2me | Theorems.Thm_NQueensComp_NPC_observation_29
-- name    : NQueensComp.NPC.observation_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:24.019084+00:00
-- url     : https://prove2.me/theorems/8270ea26-cbf7-4a31-9ab2-0998997fa3c1
-- title:
--   Observation 29 — 21(c₁−c₂) ± 7(a₁−a₂) ± (d₁−d₂) = 0 forces c₁ = c₂, a₁ = a₂, d₁ = d₂
-- statement:
--   **Observation 29.** Let $a_1,a_2,c_1,c_2,d_1,d_2$ be integers with $0\le a_1,a_2\le2$ and $0\le d_1,d_2\le6$, and let $s_1,s_2\in\{1,-1\}$. If
--   $$21(c_1-c_2)+s_1\cdot7(a_1-a_2)+s_2(d_1-d_2)=0,$$
--   then $c_1=c_2$, $a_1=a_2$ and $d_1=d_2$.
--
--   The column spacing $21$ between variable gadgets and the row spacing $7$ inside clause gadgets were chosen so that this holds; it is what makes the diagonals of different gadgets in the reduction from Restricted 1-in-3-SAT distinct (Lemmas 30 and 32).
--
--   **Formalization Note** The two printed signs $\pm$ are independent; they are the parameters $s_1,s_2$.
--
--   Differences from the source:
--   - encoding: the two signs ± in 21(c₁ − c₂) ± 7(a₁ − a₂) ± (d₁ − d₂) → independent sign parameters s₁, s₂ ∈ {1, −1}; reason: the four sign choices are exactly the four instances
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 834, Observation 29

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

namespace NQueensComp.NPC

/-- Observation 29, p. 834: for integers `a₁, a₂, c₁, c₂, d₁, d₂` with `0 ≤ a₁, a₂ ≤ 2` and
`0 ≤ d₁, d₂ ≤ 6`, if `21(c₁ − c₂) ± 7(a₁ − a₂) ± (d₁ − d₂) = 0` (either choice of each sign) then
`c₁ = c₂`, `a₁ = a₂` and `d₁ = d₂`. -/
theorem observation_29 (a₁ a₂ c₁ c₂ d₁ d₂ s₁ s₂ : ℤ)
    (ha₁ : 0 ≤ a₁ ∧ a₁ ≤ 2) (ha₂ : 0 ≤ a₂ ∧ a₂ ≤ 2) (hd₁ : 0 ≤ d₁ ∧ d₁ ≤ 6)
    (hd₂ : 0 ≤ d₂ ∧ d₂ ≤ 6) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h : 21 * (c₁ - c₂) + s₁ * (7 * (a₁ - a₂)) + s₂ * (d₁ - d₂) = 0) :
    c₁ = c₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by sorry

end NQueensComp.NPC
