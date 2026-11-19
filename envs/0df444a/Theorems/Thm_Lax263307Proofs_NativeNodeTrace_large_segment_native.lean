-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeNodeTrace_large_segment_native
-- name    : Lax263307Proofs.NativeNodeTrace.large_segment_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:29.880838+00:00
-- url     : https://prove2.me/theorems/46df31fa-6654-4c65-ab33-c16a493d629f
-- title:
--   Actual large-node initialization phase
-- statement:
--   Fix a graph, native core configuration, target, precision denominator and recursion fuel. Assume the published large-node numeric bounds, initialized graph/stack state and running phase. The phase machine performs the complete large-node initializer, preserves the required input/frame data and reaches the oracle-entry state with the declared initialization cost:
--
--   $$\mathrm{phase}_{\rm out}=4,\qquad\mathrm{LargeNodeOutput}(\sigma_{\rm out}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNodeTrace.lean, theorem large_segment (lines 133–168)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax263307Proofs.NativeNodeTrace
end Lax263307Proofs.NativeNodeTrace

theorem Lax263307Proofs.NativeNodeTrace.large_segment_native : ∀ {n : Nat} (B : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config) (D k fuel : Nat) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.K →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (Lax263307Proofs.NativeNodeParameters.guard cfg.a cfg.K cfg.b n D) k)
              cfg.b)
            (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          B →
        @LT.lt Nat instLTNat
            (Lax263307Proofs.NativeMomentSetup.guardBound n k
              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
            B →
          @LT.lt Nat instLTNat
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              B →
            @LT.lt Nat instLTNat
                (Lax263307Proofs.NativeNodePrecision.guard n D
                  (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                  (Lax263307.AlgorithmParameters.floorDenominator cfg.a cfg.K cfg.b n D)
                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                B →
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))))
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))))
                    (@OfNat.ofNat Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                  B →
                ∀ (σ : Lax808846Proofs.Imp.Env),
                  @Lax263307Proofs.NativeLargeNode.Input n B cfg.a cfg.K cfg.b D k G inst σ →
                    @Eq Nat (σ.vars "recursion.fuel") fuel →
                      @Eq Nat (σ.vars "machine.running") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                        @Eq Nat (σ.vars "machine.phase") (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                          ∃ (τ : Lax808846Proofs.Imp.Env),
                            And
                              (Lax263307Proofs.NativeMachineSegment.Segment B
                                (Lax263307Proofs.NativeCoreMachine.phases cfg)
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (Lax263307Proofs.NativeLargeNode.cost cfg.a n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                σ τ)
                              (And (@Lax263307Proofs.NativeLargeNode.Output n cfg.a cfg.K cfg.b D k G inst τ)
                                (And (@Eq Nat (τ.vars "recursion.fuel") fuel)
                                  (And
                                    (@Eq Nat (τ.vars "machine.running")
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@Eq Nat (τ.vars "machine.phase")
                                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))) := by sorry
