-- Prove2me | Theorems.Thm_OAI_Release075_large_prime_grid_outcome
-- name    : OAI.Release075.large_prime_grid_outcome
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:46:59.876135+00:00
-- url     : https://prove2.me/theorems/1805b2a4-311d-4f9f-8c9c-1b66c34cabbc
-- title:
--   A large prime gives marked lines meeting the rank budget
-- statement:
--   Let $q\ge200$ be a prime, $r=200\cdot200^{20}$ and $q\ge1000\cdot200^{20}r^2$. Let $S\subseteq\mathbb Z/q$ have $\lfloor q/100\rfloor$ elements and use the grid $S^{20}\subseteq\mathbb F_q^{20}$ as marks. Then some assignment $\omega$ of projective directions to the marks satisfies, for the threshold $T=4r^2$,
--   $$
--   4\bigl(2q^{20}+r\,|E_\omega|\bigr)<|\text{retained marks}|\cdot r ,
--   $$
--   where $E_\omega$ is the set of exceptional points and the retained marks are those not on an occurring short cycle.
--
--   Every later finite quotient is taken with respect to this same fixed prime.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L865-L894

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (q : ℕ) [Fact q.Prime]
variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

theorem OAI.Release075.large_prime_grid_outcome (r : ℕ) (hr : r = 200*200^20)
    (hq200 : 200 ≤ q) (hq : 1000*200^20*r^2 ≤ q)
    (S : Finset (ZMod q)) (hS : S.card = q/100) :
    ∃ ω : gridMarks q S → Projectivization (ZMod q) (Fin 20 → ZMod q),
      4 * (2 * Fintype.card (Fin 20 → ZMod q) +
        r * (exceptionalPoints (gridMarks q S) ω (4*r^2)).card) <
      Fintype.card (Retained (gridMarks q S) ω) * r := by sorry
