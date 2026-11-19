-- Prove2me | Theorems.Thm_Lax455465Proofs_RamVirtualExecution_execute_spec_native
-- name    : Lax455465Proofs.RamVirtualExecution.execute_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:09.087201+00:00
-- url     : https://prove2.me/theorems/7d6efbb7-b2a0-4466-abcf-c2fe3844327c
-- title:
--   Uniform native interpretation of a complete source-RAM run
-- statement:
--   Let $p$ be a finite source RAM program, $u$ a finite input-word list, and $f$ the source state reached after $k$ steps at word width $w$. Suppose the next source step is halting, input words and program literals fit the published host guards, and $2(2^w)^2+3<B$. From a stored input prefix, width and sufficient address/value/output buffers, the fixed native interpreter executes to a representation of $f$, with its running flag zero, in at most
--   $$(k+1)(4|p|+32k+104)+18$$
--   instructions. This reproduces an actual source run from zero source memory; the native buffers may initially contain stale entries.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamVirtualExecution.lean, theorem Lax455465Proofs.RamVirtualExecution.execute_spec, line 10

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamVirtualExecution
end Lax455465Proofs.RamVirtualExecution

theorem Lax455465Proofs.RamVirtualExecution.execute_spec_native : ∀ (B w k : Nat) (p : Lax808846.Ram.Program) (input : List Nat) (f : Lax455465Proofs.SparseRam.SparseState),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      B →
    @LT.lt Nat instLTNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        B →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Lax808846.Ram.Instr p)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          B →
        (∀ (i : Lax808846.Ram.Instr),
            @Membership.mem Lax808846.Ram.Instr Lax808846.Ram.Program (@List.instMembership Lax808846.Ram.Instr) p i →
              Lax455465Proofs.RamVirtualInstruction.LiteralsFit
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) B
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i) →
          @LT.lt Nat instLTNat (@List.length Nat input) B →
            (∀ (x : Nat),
                @Membership.mem Nat (List Nat) (@List.instMembership Nat) input x → @LT.lt Nat instLTNat x B) →
              @Eq (Option Lax455465Proofs.SparseRam.SparseState)
                  (Lax455465Proofs.SparseRam.run w p k (Lax455465Proofs.SparseRam.init input))
                  (@Option.some Lax455465Proofs.SparseRam.SparseState f) →
                @Eq (Option Lax455465Proofs.SparseRam.SparseState) (Lax455465Proofs.SparseRam.step w p f)
                    (@Option.none Lax455465Proofs.SparseRam.SparseState) →
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                      And (@Eq Nat (σ.vars "vm.width") w)
                        (And (Lax455465Proofs.RamVirtualState.Prefix input "vm.input" σ)
                          (And (@Eq Nat (σ.vars "vm.inputLength") (@List.length Nat input))
                            (And (@LT.lt Nat instLTNat k (@List.length Nat (σ.arrs "vm.addresses")))
                              (And (@LT.lt Nat instLTNat k (@List.length Nat (σ.arrs "vm.values")))
                                (@LT.lt Nat instLTNat k (@List.length Nat (σ.arrs "vm.output"))))))))
                    (Lax455465Proofs.RamVirtualProgram.execute p)
                    (fun (x τ : Lax808846Proofs.Imp.Env) =>
                      And (Lax455465Proofs.RamVirtualState.Represents w f τ)
                        (@Eq Nat (τ.vars "vm.running") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@List.length Lax808846.Ram.Instr p))
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) k))
                          (@OfNat.ofNat Nat (nat_lit 104) (instOfNatNat (nat_lit 104)))))
                      (@OfNat.ofNat Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))) := by sorry
