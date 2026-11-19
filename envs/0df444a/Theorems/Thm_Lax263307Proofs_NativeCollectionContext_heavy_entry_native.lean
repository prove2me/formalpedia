-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCollectionContext_heavy_entry_native
-- name    : Lax263307Proofs.NativeCollectionContext.heavy_entry_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:03.220285+00:00
-- url     : https://prove2.me/theorems/69d3ac5e-c3b8-4999-b53a-cacda6cf642e
-- title:
--   Enter the heavy branch of a native collection iteration
-- statement:
--   Let $G$ have $n>0$ vertices, $x$ be a bounded nonnegative rational weight vector, and $C_i$ the current part in a list of at most $n+1$ parts. Assume the complete collection context, positive accuracy denominator $D$, index and buffer guards. If
--   $$\sum_{v\in C_i}x_v>\frac{k}{4nD},$$
--   two native phase transitions prepare the restricted graph, current union, exact component target and phase-$11$ recursive entry, while retaining the full context and collection anchor. Their time is at most $43n+33+T_{\rm component}(n,h)$.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCollectionContext.lean, theorem Lax263307Proofs.NativeCollectionContext.heavy_entry, line 152

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax263307Proofs.NativeCollectionContext
end Lax263307Proofs.NativeCollectionContext

theorem Lax263307Proofs.NativeCollectionContext.heavy_entry_native : ∀ (n D k r fuel stride h : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x : Fin n → NNRat)
  (parts : List (Finset (Fin n))) (A : Finset (Fin n)) (extent : String → Nat) (front : List Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
      (∀ (v : Fin n),
          Lax263307Proofs.NativeSignedArithmetic.Bounded
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
            (@NNRat.cast Rat Rat.instNNRatCast (x v))) →
        ∀ (w : Nat),
          @LE.le Nat instLENat (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w →
            @LE.le Nat instLENat (@List.length (Finset (Fin n)) parts)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              ∀ (i : Nat) (hi : @LT.lt Nat instLTNat i (@List.length (Finset (Fin n)) parts)),
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i (@List.length (Finset (Fin n)) parts))
                      (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                  @LE.le Nat instLENat n (extent "subset.bits") →
                    @LE.le Nat instLENat n (extent "restrict.vertices") →
                      @LT.lt Nat instLTNat
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n)
                          (extent "lp.word") →
                        @LE.le Nat instLENat
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n)
                            (extent "sum.input") →
                          @LT.lt Rat Rat.instLT
                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                    (@Nat.cast Rat Rat.instNatCast D))
                                  (@Nat.cast Rat Rat.instNatCast k))
                                (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                  (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                  (@Nat.cast Rat Rat.instNatCast n)))
                              (∑
                                v ∈
                                  @GetElem.getElem (List (Finset (Fin n))) Nat (Finset (Fin n))
                                    (fun (as : List (Finset (Fin n))) (i : Nat) =>
                                      @LT.lt Nat instLTNat i (@List.length (Finset (Fin n)) as))
                                    (@List.instGetElemNatLtLength (Finset (Fin n))) parts i hi,
                                @NNRat.cast Rat Rat.instNNRatCast (x v)) →
                            ∀ (U : Finset (Fin n)) (σ : Lax808846Proofs.Imp.Env),
                              @Lax263307Proofs.NativeCollectionTrace.At n
                                  (@Lax263307Proofs.NativeCollectionContext.Context n
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                    D k r fuel stride G inst x parts A extent front)
                                  i U σ →
                                ∃ (τ : Lax808846Proofs.Imp.Env),
                                  And
                                    (Lax263307Proofs.NativeMachineSegment.Segment
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                      (Lax263307Proofs.NativeCoreMachine.phases cfg)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 43) (instOfNatNat (nat_lit 43))) n)
                                          (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33))))
                                        (Lax263307Proofs.NativeComponentDecision.timeBound n h))
                                      σ τ)
                                    (And
                                      (@Lax263307Proofs.NativeCollectionContext.Context n
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                        D k r fuel stride G inst x parts A extent front τ)
                                      (And
                                        (@Lax263307Proofs.NativeRestrictionRead.Data n G inst
                                          (fun (v : Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v))
                                          (@GetElem.getElem (List (Finset (Fin n))) Nat (Finset (Fin n))
                                            (fun (as : List (Finset (Fin n))) (i : Nat) =>
                                              @LT.lt Nat instLTNat i (@List.length (Finset (Fin n)) as))
                                            (@List.instGetElemNatLtLength (Finset (Fin n))) parts i hi)
                                          τ)
                                        (And
                                          (@Eq Nat (τ.vars "component.mask")
                                            (@Lax263307Proofs.NativeMasks.mask n
                                              (@GetElem.getElem (List (Finset (Fin n))) Nat (Finset (Fin n))
                                                (fun (as : List (Finset (Fin n))) (i : Nat) =>
                                                  @LT.lt Nat instLTNat i (@List.length (Finset (Fin n)) as))
                                                (@List.instGetElemNatLtLength (Finset (Fin n))) parts i hi)))
                                          (And (@Eq Nat (τ.vars "component.i") i)
                                            (And
                                              (@Eq Nat (τ.vars "component.union")
                                                (@Lax263307Proofs.NativeMasks.mask n U))
                                              (And
                                                (@Eq Nat (τ.vars "component.target")
                                                  (Lax263307.ComputedRounding.target
                                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                      (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                      (@Nat.cast Rat Rat.instNatCast D))
                                                    (∑
                                                      v ∈
                                                        @GetElem.getElem (List (Finset (Fin n))) Nat (Finset (Fin n))
                                                          (fun (as : List (Finset (Fin n))) (i : Nat) =>
                                                            @LT.lt Nat instLTNat i (@List.length (Finset (Fin n)) as))
                                                          (@List.instGetElemNatLtLength (Finset (Fin n))) parts i hi,
                                                      @NNRat.cast Rat Rat.instNNRatCast (x v))))
                                                (And
                                                  (@Eq Nat (τ.vars "machine.running")
                                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (And
                                                    (@Eq Nat (τ.vars "machine.phase")
                                                      (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                                                    (Lax263307Proofs.NativeCollectionAnchor.Anchor σ τ))))))))) := by sorry
