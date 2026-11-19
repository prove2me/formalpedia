-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSolverTotalExecution_solve_spec_native
-- name    : Lax109476Proofs.RamSolverTotalExecution.solve_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:45.430199+00:00
-- url     : https://prove2.me/theorems/7da81dae-ab47-45ee-b787-ef807906be1a
-- title:
--   Total native LP-solver execution on arbitrary word input
-- statement:
--   Let $x$ be any finite natural-word list, including malformed encodings, and let $L$ be its binary size. Assume $w\ge W(L)$ and the complete initialized frontend and solver workspace. The fixed command has at most $T(L)$ instructions and returns its full outcome: invalid input has validity flag zero and unchanged output, while valid decoded input receives a valid encoded certificate. Thus
--
--   $$\mathrm{Spec}_{2^w}(\mathrm{Input}_x,\mathrm{solve},\mathrm{Result}_x,T(L)).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSolverTotalExecution.lean, theorem solve_spec (lines 25–65)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamSolverTotalExecution
end Lax109476Proofs.RamSolverTotalExecution

theorem Lax109476Proofs.RamSolverTotalExecution.solve_spec_native : ∀ (xs : List Nat) (w : Nat),
  @LE.le Nat instLENat (Lax109476Proofs.RamUniformSolverBounds.wordWidth (Lax759944.BinaryWordEncoding.bitSize xs)) w →
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (Lax109476Proofs.RamSolverTotalExecution.Input
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        xs)
      Lax109476Proofs.RamExactSolverProgram.solve (Lax109476Proofs.RamSolverTotalExecution.Result xs)
      (Lax109476Proofs.RamUniformSolverBounds.instructionBound (Lax759944.BinaryWordEncoding.bitSize xs)) := by sorry
