-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeQptasPositive_command_spec_native
-- name    : Lax263307Proofs.NativeQptasPositive.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:43.608994+00:00
-- url     : https://prove2.me/theorems/6ccd05ac-3076-442a-b9d6-990de629521b
-- title:
--   Actual weighted native execution with nonzero blow-up order
-- statement:
--   Fix the selected native implementation, a graph, arbitrary signed rational weights and positive rational accuracy. Assume the positive rounded blow-up order case and all published numeric, word-width, initialization and allocated-extent guards. The fixed weighted command returns exactly the functional weighted answer, with its complete charged instruction bound:
--
--   $$\mathrm{Spec}_{2^w}(\mathrm{WeightedInput},c_{\rm weighted},\mathrm{EncodedFunctionalAnswer},T).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeQptasPositive.lean, theorem command_spec (lines 84–210)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeQptasPositive
end Lax263307Proofs.NativeQptasPositive

theorem Lax263307Proofs.NativeQptasPositive.command_spec_native : ∀ {C : Lax263307.GraphClasses.GraphClass} (i : Lax263307Proofs.NativeQptasImplementation.Fixed C) {n : Nat}
  (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
  @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n))) (C n)
      G →
    ∀ (weights : Fin n → Rat) (ε : Rat),
      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε →
        ∀ (M w : Nat),
          @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
            @LE.le Nat instLENat n M →
              (∀ (v : Fin n), Lax263307Proofs.NativeSignedArithmetic.Bounded M (weights v)) →
                Lax263307Proofs.NativeSignedArithmetic.Bounded M ε →
                  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                      (@Lax263307Proofs.NativeQptasPositive.order n weights ε) →
                    @Lax263307Proofs.NativeQptasPositive.Bounds C i n
                        (@Lax263307Proofs.NativeQptasPositive.order n weights ε) M w ε →
                      have N := @Lax263307Proofs.NativeQptasPositive.order n weights ε;
                      have W := @Lax263307Proofs.NativeQptasPositive.workspace C i N ε;
                      have ext :=
                        Lax263307Proofs.NativeRootWorkspace.extent
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i) N W n;
                      Lax808846Proofs.Reasoning.Spec
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                        (fun (σ : Lax808846Proofs.Imp.Env) =>
                          And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                            (And
                              (Lax263307Proofs.NativeStateBounds.Bounded
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                σ)
                              (∀ (a : String), @Eq Nat (@List.length Nat (σ.arrs a)) (ext a))))
                        (Lax263307Proofs.NativeQptasProgram.command
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeExponent C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetExponent C i))
                        (fun (σ τ : Lax808846Proofs.Imp.Env) =>
                          @Eq (List Nat) τ.out
                            (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                              (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                              (@Lax263307.IndependentSetEncoding.encodeOutput n
                                (@Lax263307.WeightedAlgorithm.solve n
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.lp C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.flow C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).a
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).K
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).b G inst weights ε))))
                        (@Lax263307Proofs.NativeQptasPositive.cost C i n N ε) := by sorry
