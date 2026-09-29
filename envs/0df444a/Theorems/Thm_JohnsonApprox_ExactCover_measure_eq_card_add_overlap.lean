-- Prove2me | Theorems.Thm_JohnsonApprox_ExactCover_measure_eq_card_add_overlap
-- name    : JohnsonApprox.ExactCover.measure_eq_card_add_overlap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:31:24.118183+00:00
-- url     : https://prove2.me/theorems/b3a80de1-5d3d-4f43-9b7f-c1badc772b56
-- title:
--   Proof of Theorem 6 — the measure of C2's output is |T| plus the cumulative overlap
-- statement:
--   Let $F$ be an input of SET COVERING II with covered set $T = \bigcup_{S \in F} S$. Consider a run of algorithm C2 on $F$ that halts, and let $F_1$ be the subcover it returns. For each $S \in F_1$ let the **overlap** $\mathrm{ov}(S)$ be the value of $|S - \mathrm{UNCOV}|$ at the moment $S$ was added to SUB, and let $\mathrm{OV}(F_1) = \sum_{S\in F_1} \mathrm{ov}(S)$ be the cumulative overlap. Then
--   $$m_{EC}(F_1) = |T| + \mathrm{OV}(F_1).$$
--
--   Every point of $T$ is newly covered by exactly one chosen set, and the other points of a chosen set are its overlap. The identity converts the analysis of C2 into a bound on the cumulative overlap.
--
--   **Formalization Note** A run with cumulative overlap $v$ ending in state $\sigma$ is `RunOV F σ v`; halting is `UNCOV = ∅`, and the returned subcover is `σ.SUB`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 271, proof of Theorem 6

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem
import Definitions.Def_JohnsonApprox_ExactCover_C2

namespace JohnsonApprox.ExactCover

/-- Proof of Theorem 6 (p. 271): for a run of C2 that halts, `m(F₁) = |T| + OV(F₁)`. -/
theorem measure_eq_card_add_overlap {α : Type} [DecidableEq α] (F : Input α)
    {σ : State F} {ov : ℕ} (hrun : RunOV F σ ov) (hσ : Halts σ) :
    F.measure σ.SUB = F.ground.card + ov := by sorry

end JohnsonApprox.ExactCover
