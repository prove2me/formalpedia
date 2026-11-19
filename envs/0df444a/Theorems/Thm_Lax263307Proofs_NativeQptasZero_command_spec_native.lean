-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeQptasZero_command_spec_native
-- name    : Lax263307Proofs.NativeQptasZero.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:42.862797+00:00
-- url     : https://prove2.me/theorems/89fd1ee5-a730-4379-9ce1-16a001c86a00
-- title:
--   Actual weighted native execution with zero blow-up order
-- statement:
--   Fix the selected native implementation, a graph, arbitrary signed rational weights and positive rational accuracy. Assume the zero rounded blow-up order case and all published numeric, word-width, initialization and allocated-extent guards. The fixed weighted command returns exactly the functional weighted answer, with its complete charged instruction bound:
--
--   $$\mathrm{Spec}_{2^w}(\mathrm{WeightedInput},c_{\rm weighted},\mathrm{EncodedFunctionalAnswer},T).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeQptasZero.lean, theorem command_spec (lines 13–46)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeQptasZero
end Lax263307Proofs.NativeQptasZero

theorem Lax263307Proofs.NativeQptasZero.command_spec_native : ∀ {n : Nat} (B M : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat n M →
      ∀ (cfg : Lax263307Proofs.NativeCoreMachine.Config) (C d Q e : Nat) (lp flow : List Nat → List Nat)
        (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
        (weights : Fin n → Rat) (ε : Rat),
        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε →
          (∀ (v : Fin n),
              And (@LE.le Nat instLENat (weights v).num.natAbs M) (@LE.le Nat instLENat (weights v).den M)) →
            And (@LE.le Nat instLENat ε.num.natAbs M) (@LE.le Nat instLENat ε.den M) →
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        M (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  B →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    B →
                  @Eq Nat
                      (∑ v : Fin n,
                        @Lax263307.WeightRounding.copies n (@Lax263307.PositiveWeights.positiveWeights n weights) ε v)
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                          (And
                            (@LE.le Nat instLENat
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
                                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@List.length Nat (σ.arrs "input.data")))
                            (And (@LE.le Nat instLENat n (@List.length Nat (σ.arrs "copy.counts")))
                              (@Eq Nat (@List.length Nat (σ.arrs "weighted.output")) n))))
                      (Lax263307Proofs.NativeQptasProgram.command cfg C d Q e)
                      (fun (σ τ : Lax808846Proofs.Imp.Env) =>
                        @Eq (List Nat) τ.out
                          (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                            (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                            (@Lax263307.IndependentSetEncoding.encodeOutput n
                              (@Lax263307.WeightedAlgorithm.solve n lp flow cfg.a cfg.K cfg.b G inst weights ε))))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (Lax263307Proofs.NativeBlowUp.cost n
                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) n))
                        (@OfNat.ofNat Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) := by sorry
