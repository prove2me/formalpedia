-- Prove2me | Theorems.Thm_Lax109476Proofs_RationalFeasibilityDecision_feasible_correct_native
-- name    : Lax109476Proofs.RationalFeasibilityDecision.feasible_correct_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:00.510291+00:00
-- url     : https://prove2.me/theorems/8bfa4207-4204-4441-9c6e-83c77cc04969
-- title:
--   Correctness of the total exact rational feasibility decision
-- statement:
--   For every rational linear program $P$, including zero-dimensional and infeasible systems, the source's total computable rational ellipsoid decision satisfies
--   $$\operatorname{feasible}(P)=\operatorname{true}\quad\Longleftrightarrow\quad\exists x\in\mathbb R^n,\ x\ge0\ \land\ A_Px\le b_P.$$
--   The decision clears rational denominators and uses padded integer feasibility; there is no dimension or feasibility promise. This semantic theorem connects the Boolean used by native recovery queries to real feasibility.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RationalFeasibilityDecision.lean, theorem Lax109476Proofs.RationalFeasibilityDecision.feasible_correct, line 59

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax109476Proofs.RationalFeasibilityDecision
end Lax109476Proofs.RationalFeasibilityDecision

theorem Lax109476Proofs.RationalFeasibilityDecision.feasible_correct_native : ∀ {m n : Nat} (P : Lax109476.LinearProgram.Program Rat m n),
  Iff (@Eq Bool (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P) Bool.true)
    (@Lax109476.LinearProgram.IsFeasible m n (@Lax109476.RationalCertificates.toReal m n P)) := by sorry
