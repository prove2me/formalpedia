-- Prove2me | Theorems.Thm_Lax109476Proofs_RamStoredFeasibility_decideFeasible_condition_spec
-- name    : Lax109476Proofs.RamStoredFeasibility.decideFeasible_condition_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:10:15.665985+00:00
-- url     : https://prove2.me/theorems/cfa591b6-de25-4d8e-b89e-70a19e6a5f05
-- title:
--   Execution of exact feasibility for a stored rational program
-- statement:
--   Let $P$ be a rational linear program with $m$ constraints and $n$ variables, and write $L$ for the binary length of its published encoding. Let $w$ be at least the prescribed stored-feasibility word-width function at $L$. Starting from the stored-program input and allocated workspace, the deterministic feasibility command returns a condition with exactly the mathematical feasibility value:
--   $$\operatorname{eval}_{2^w}(\text{search.found}=1)=\operatorname{some}(\operatorname{feasible}(P)).$$
--   The actual execution is bounded by the published instruction-bound function at $L$. The feasibility predicate concerns the constraints of $P$, without any assumption on its objective coefficients. This is the reusable operational interface used by the certificate-system decision routine.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamStoredFeasibility.lean, theorem decideFeasible_condition_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

theorem Lax109476Proofs.RamStoredFeasibility.decideFeasible_condition_spec : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (w : ℕ),
  Lax109476Proofs.RamStoredFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P)) ≤
      w →
    Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamStoredFeasibility.Input P)
      Lax109476Proofs.RamStoredFeasibility.decideFeasible
      (fun (x τ : Lax808846Proofs.Imp.Env) =>
        Lax808846Proofs.Imp.Cond.evalB (2 ^ w)
            (Lax808846Proofs.Imp.Cond.eq (Lax808846Proofs.Imp.Expr.var "search.found") (Lax808846Proofs.Imp.Expr.lit 1))
            τ =
          Option.some (Lax109476Proofs.RationalFeasibilityDecision.feasible P))
      (Lax109476Proofs.RamStoredFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))) := by sorry
