-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRationalFeasibility_decideFeasible_with_flag_spec_native
-- name    : Lax109476Proofs.RamRationalFeasibility.decideFeasible_with_flag_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:15.42005+00:00
-- url     : https://prove2.me/theorems/5d7d4ab0-f070-4da5-8eb5-0bfd0e668001
-- title:
--   Rational feasibility execution with a Boolean output flag
-- statement:
--   Let $P$ be a rational linear program with $m$ constraints and $n$ variables, and let $L$ be the binary size of its encoding. Suppose $w$ is at least the published feasibility word-width bound $W(L)$ and the complete input and workspace predicate holds. The fixed rational feasibility command terminates within $T(L)$ instructions and produces a genuine Boolean flag $b$ satisfying
--   $$b\le1,\qquad(b=1)\Longleftrightarrow\operatorname{feasible}(P).$$
--   Here feasibility is the source's total exact decision predicate, and the bound and decision are uniform in all rational input data. Retaining the Boolean range is needed to use the flag in actual conditional execution.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFeasibilityFlags.lean, theorem Lax109476Proofs.RamRationalFeasibility.decideFeasible_with_flag_spec, line 114

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax109476Proofs.RamRationalFeasibility
end Lax109476Proofs.RamRationalFeasibility

theorem Lax109476Proofs.RamRationalFeasibility.decideFeasible_with_flag_spec_native : ∀ (m n : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (w : Nat),
  @LE.le Nat instLENat
      (Lax109476Proofs.RamRationalFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w →
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamRationalFeasibility.decideFeasible
      (fun (x τ : Lax808846Proofs.Imp.Env) =>
        And (@LE.le Nat instLENat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (instDecidableEqNat (τ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P)))
      (Lax109476Proofs.RamRationalFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))) := by sorry
