-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCollectionExecution_iterations_native
-- name    : Lax263307Proofs.NativeCollectionExecution.iterations_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:58.831465+00:00
-- url     : https://prove2.me/theorems/491ea671-858f-4bab-b3ab-85a83a16fbec
-- title:
--   Prefix invariant for native recursive part collection
-- statement:
--   Fix a finite indexed family of graph parts and the bounded child-execution contract. Under the complete collection invariant and input-frame guards, every eligible iterator prefix has an actual segment realizing the same functional prefix collection. The segment retains the graph, parent and collection state, with the stated affine bounds in prefix length and child costs:
--
--   $$\mathrm{storedPrefix}_j=\operatorname{collectPrefix}(j,\mathrm{parts},\mathrm{child}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCollectionExecution.lean, theorem iterations (lines 46–123)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeCollectionExecution
end Lax263307Proofs.NativeCollectionExecution

theorem Lax263307Proofs.NativeCollectionExecution.iterations_native : ∀ {n : Nat} {ι : Type} (D k r fuel S h T childSteps childTime : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x : Fin n → NNRat)
  (parts : ι → Finset (Fin n)) (order : List ι) (A : Finset (Fin n)) (extent : String → Nat) (front : List Nat)
  (base : Lax808846Proofs.Imp.Env)
  (child : (C : Finset (Fin n)) → Nat → Option (Finset (Fin (@Finset.card (Fin n) C)))),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
      (∀ (v : Fin n),
          Lax263307Proofs.NativeSignedArithmetic.Bounded
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
            (@NNRat.cast Rat Rat.instNNRatCast (x v))) →
        ∀ (w : Nat),
          @LE.le Nat instLENat (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w →
            @LE.le Nat instLENat (@List.length ι order)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              @LT.lt Nat instLTNat
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                                    (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length ι order)))
                            T)
                          fuel)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (Lax263307Proofs.NativeCatalogMetadata.N n r)))
                      (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                  (∀ (i : ι),
                      @Membership.mem ι (List ι) (@List.instMembership ι) order i →
                        @LE.le Nat instLENat
                          (Lax263307.ComputedRounding.target
                            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                              (@Nat.cast Rat Rat.instNatCast D))
                            (∑ v ∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)))
                          T) →
                    (∀ (a : String),
                        @Membership.mem String (List String) (@List.instMembership String)
                            (Lax263307Proofs.NativeCoreMachine.frameArrays cfg) a →
                          @Eq Nat (extent a) S) →
                      @LE.le Nat instLENat
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                            (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                          (extent "recursion.frames") →
                        @LE.le Nat instLENat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                            (extent "child.graph") →
                          @LE.le Nat instLENat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                              (extent "search.graph") →
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
                                    @LE.le Nat instLENat
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                        (extent "lp.input") →
                                      @LE.le Nat instLENat
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                            (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                          (extent "round.normal") →
                                        (∀ (i : ι),
                                            @Membership.mem ι (List ι) (@List.instMembership ι) order i →
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
                                                  (∑ v ∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)) →
                                                ∀ (σ : Lax808846Proofs.Imp.Env),
                                                  @Lax263307Proofs.NativeCollectionExecution.Invariant n
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                                      D k r fuel S G inst x (@List.map ι (Finset (Fin n)) parts order) A
                                                      extent front base σ →
                                                    @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                                                        (fun (v : Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v))
                                                        (parts i) σ →
                                                      @Eq Nat (σ.vars "component.mask")
                                                          (@Lax263307Proofs.NativeMasks.mask n (parts i)) →
                                                        @Eq Nat (σ.vars "component.target")
                                                            (Lax263307.ComputedRounding.target
                                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                (@OfNat.ofNat Rat (nat_lit 1)
                                                                  (@Rat.instOfNat (nat_lit 1)))
                                                                (@Nat.cast Rat Rat.instNatCast D))
                                                              (∑ v ∈ parts i,
                                                                @NNRat.cast Rat Rat.instNNRatCast (x v))) →
                                                          @Eq Nat (σ.vars "machine.running")
                                                              (@OfNat.ofNat Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))) →
                                                            @Eq Nat (σ.vars "machine.phase")
                                                                (@OfNat.ofNat Nat (nat_lit 11)
                                                                  (instOfNatNat (nat_lit 11))) →
                                                              @Lax263307Proofs.NativeCollectionChild.Recursive n
                                                                (@HPow.hPow Nat Nat Nat
                                                                  (@instHPow Nat Nat
                                                                    (@NPow.toPow Nat
                                                                      (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                  (@OfNat.ofNat Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  w)
                                                                S fuel childSteps childTime cfg G inst (parts i)
                                                                (Lax263307.ComputedRounding.target
                                                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                    (@OfNat.ofNat Rat (nat_lit 1)
                                                                      (@Rat.instOfNat (nat_lit 1)))
                                                                    (@Nat.cast Rat Rat.instNatCast D))
                                                                  (∑ v ∈ parts i,
                                                                    @NNRat.cast Rat Rat.instNNRatCast (x v)))
                                                                front σ
                                                                (child (parts i)
                                                                  (Lax263307.ComputedRounding.target
                                                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                                      (@OfNat.ofNat Rat (nat_lit 1)
                                                                        (@Rat.instOfNat (nat_lit 1)))
                                                                      (@Nat.cast Rat Rat.instNatCast D))
                                                                    (∑ v ∈ parts i,
                                                                      @NNRat.cast Rat Rat.instNNRatCast (x v))))) →
                                          @Lax263307Proofs.NativeCollectionTrace.Iterations n ι
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                            cfg
                                            (@Lax263307Proofs.NativeCollectionExecution.Invariant n
                                              (@HPow.hPow Nat Nat Nat
                                                (@instHPow Nat Nat
                                                  (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                              D k r fuel S G inst x (@List.map ι (Finset (Fin n)) parts order) A extent
                                              front base)
                                            (@Lax263307Proofs.NativeCollectionExecution.Cut n r A) parts
                                            (fun (i : ι) =>
                                              @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                                                (Lax263307.ComputedRounding.target
                                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                    (@Nat.cast Rat Rat.instNatCast D))
                                                  (∑ v ∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v)))
                                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@Lax263307.ComputedRounding.answer n ι
                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                                (@Nat.cast Rat Rat.instNatCast D))
                                              k (fun (i : ι) => ∑ v ∈ parts i, @NNRat.cast Rat Rat.instNNRatCast (x v))
                                              fun (i : ι) (t : Nat) =>
                                              @Option.map (Finset (Fin (@Finset.card (Fin n) (parts i))))
                                                (Finset (Fin n))
                                                (fun (I : Finset (Fin (@Finset.card (Fin n) (parts i)))) =>
                                                  @Finset.image (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                    (instDecidableEqFin n)
                                                    (@DFunLike.coe
                                                      (@OrderEmbedding (Fin (@Finset.card (Fin n) (parts i))) (Fin n)
                                                        (@instLEFin (@Finset.card (Fin n) (parts i))) (@instLEFin n))
                                                      (Fin (@Finset.card (Fin n) (parts i)))
                                                      (fun (x : Fin (@Finset.card (Fin n) (parts i))) => Fin n)
                                                      (@instFunLikeOrderEmbedding (Fin (@Finset.card (Fin n) (parts i)))
                                                        (Fin n) (@instLEFin (@Finset.card (Fin n) (parts i)))
                                                        (@instLEFin n))
                                                      (@Lax263307.ComputedSeparators.label n (parts i)))
                                                    I)
                                                (child (parts i) t))
                                            order
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) childSteps
                                              (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                            (Lax263307Proofs.NativeCollectionExecution.partCost cfg n r S h childTime) := by sorry
