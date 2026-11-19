-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRationalFeasibility_decideFeasible_spec_native
-- name    : Lax109476Proofs.RamRationalFeasibility.decideFeasible_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:44.942838+00:00
-- url     : https://prove2.me/theorems/6a0d28d1-da4a-40d5-ad03-2f75f2a07eb5
-- title:
--   Total rational feasibility from the stored query interface
-- statement:
--   Let $P$ be a rational LP and $L$ its canonical binary encoding size. Assume the complete stored feasibility-query input and $w\ge W(L)$. The same fixed rational feasibility command halts within $T(L)$ instructions and returns precisely the feasibility decision for the constraints of $P$:
--
--   $$\operatorname{decide}(\mathrm{search.found}=1)=\operatorname{feasible}(P).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRationalFeasibility.lean, theorem decideFeasible_spec (lines 18–36)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamRationalFeasibility
end Lax109476Proofs.RamRationalFeasibility

theorem Lax109476Proofs.RamRationalFeasibility.decideFeasible_spec_native : ∀ (m n : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (w : Nat),
  @LE.le Nat instLENat
      (Lax109476Proofs.RamRationalFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w →
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamRationalFeasibility.decideFeasible
      (fun (x τ : Lax808846Proofs.Imp.Env) =>
        @Eq Bool
          (@Decidable.decide (@Eq Nat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (instDecidableEqNat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P))
      (Lax109476Proofs.RamRationalFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))) := by sorry
