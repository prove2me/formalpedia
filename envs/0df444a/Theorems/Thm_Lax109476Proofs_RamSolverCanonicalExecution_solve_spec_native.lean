-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSolverCanonicalExecution_solve_spec_native
-- name    : Lax109476Proofs.RamSolverCanonicalExecution.solve_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:21.954196+00:00
-- url     : https://prove2.me/theorems/d3b22303-572a-4194-8514-9d73b2e145ae
-- title:
--   Native exact LP execution for a canonical rational program
-- statement:
--   Let $P$ be a rational LP and $L$ the size of its canonical encoding. With $w\ge W(L)$ and the published initialized source and workspace predicates, the actual solver command produces its complete certificate result within $T(L)$ instructions:
--
--   $$\mathrm{Spec}_{2^w}(\mathrm{Input}_P,\mathrm{solve},\mathrm{CertificateResult}_P,T(L)).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSolverCanonicalExecution.lean, theorem solve_spec (lines 22–55)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamSolverCanonicalExecution
end Lax109476Proofs.RamSolverCanonicalExecution

theorem Lax109476Proofs.RamSolverCanonicalExecution.solve_spec_native : ∀ (m n w : Nat) (P : Lax109476.LinearProgram.Program Rat m n),
  @LE.le Nat instLENat
      (Lax109476Proofs.RamUniformSolverBounds.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w →
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@Lax109476Proofs.RamSolverCanonicalExecution.Input m n
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
        P)
      Lax109476Proofs.RamExactSolverProgram.solve (@Lax109476Proofs.RamSolverFinish.Result m n P)
      (Lax109476Proofs.RamUniformSolverBounds.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))) := by sorry
