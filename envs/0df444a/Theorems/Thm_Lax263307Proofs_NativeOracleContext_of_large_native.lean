-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeOracleContext_of_large_native
-- name    : Lax263307Proofs.NativeOracleContext.of_large_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:40.000953+00:00
-- url     : https://prove2.me/theorems/62386628-024d-4a09-b896-7145f195d01a
-- title:
--   Oracle context and initial rounded state from a large node
-- statement:
--   Let a native state satisfy the completed large-node output and the complete bounded protocol, storage-length, stack, stride and frame hypotheses. That same state satisfies the full oracle-search context and stores the canonical initial rounded state:
--
--   $$\mathrm{Context}(\sigma)\ \land\ \mathrm{StoredState}_{0,(1,0)}(\sigma).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOracleContext.lean, theorem of_large (lines 157–182)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeOracleContext
end Lax263307Proofs.NativeOracleContext

theorem Lax263307Proofs.NativeOracleContext.of_large_native : ∀ {n : Nat} (B D k fuel S v : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (extent : String → Nat) (front : List Nat)
  (σ : Lax808846Proofs.Imp.Env),
  @Lax263307Proofs.NativeLargeNode.Output n cfg.a cfg.K cfg.b D k G inst σ →
    Lax263307Proofs.NativeStateBounds.Bounded B σ →
      (∀ (a : String), @Eq Nat (@List.length Nat (σ.arrs a)) (extent a)) →
        Lax455465Proofs.RamVirtualState.Prefix front "recursion.frames" σ →
          @Eq Nat (σ.vars "stack.words") (@List.length Nat front) →
            @Eq Nat (σ.vars "recursion.stride") S →
              @Eq Nat (σ.vars "recursion.fuel")
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) fuel
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                @Eq Nat (σ.vars "algorithm.roundWidth") v →
                  @Eq Nat (σ.vars "frame.length")
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg))) →
                    And
                      (@Lax263307Proofs.NativeOracleContext.Context n B D k
                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                        (Lax263307.AlgorithmParameters.load cfg.b n D)
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (Lax263307.AlgorithmParameters.floorDenominator cfg.a cfg.K cfg.b n D)
                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                        fuel S v (Lax263307.AlgorithmParameters.iterations cfg.a cfg.K cfg.b n D) cfg G inst extent
                        front σ)
                      (@Lax263307Proofs.NativeRoundedTrace.StoredState
                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@Prod.mk
                          (Matrix
                            (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                            (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                            Rat)
                          (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)) →
                            Rat)
                          (@OfNat.ofNat
                            (Matrix
                              (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                              (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                              Rat)
                            (nat_lit 1)
                            (@One.toOfNat1
                              (Matrix
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                Rat)
                              (@Matrix.one
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                Rat
                                (instDecidableEqFin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                                (@AddMonoidWithOne.toOne Rat
                                  (@AddGroupWithOne.toAddMonoidWithOne Rat
                                    (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))
                          (@OfNat.ofNat
                            (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)) →
                              Rat)
                            (nat_lit 0)
                            (@Zero.toOfNat0
                              (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)) →
                                Rat)
                              (@Pi.instZero
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (fun
                                    (a :
                                      Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))) =>
                                  Rat)
                                fun
                                  (i :
                                    Fin
                                      (Lax263307.MomentLP.dimension n
                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))) =>
                                @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
                        σ) := by sorry
