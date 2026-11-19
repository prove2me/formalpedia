-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedRounds_rounds_native
-- name    : Lax263307Proofs.NativeSelectedRounds.rounds_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:07.445638+00:00
-- url     : https://prove2.me/theorems/5e950cb3-6981-4239-a8a1-4b3912317e1b
-- title:
--   Instantiate every native recursive oracle round
-- statement:
--   Fix a hereditary graph class, selected native LP and separator programs with their encoding and correctness contracts, and a fixed machine configuration. Consider an eligible large recursive node with graph $G$, accuracy denominator $D\ge4$, fuel, target and the complete published state/resource bounds. Given the selected rounded-update program, every permitted round has the required native setup, rounding, execution and transition invariants:
--   $$\operatorname{Rounds}(G,D,k,\operatorname{fuel},\operatorname{programs},\operatorname{bounds}).$$
--   This contract covers the complete finite sequence of rounds, including smaller-fuel child calls. It is constructed from the selected programs and the explicitly quantified numerical guards.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedRounds.lean, theorem Lax263307Proofs.NativeSelectedRounds.rounds, line 75

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeSelectedRounds
end Lax263307Proofs.NativeSelectedRounds

theorem Lax263307Proofs.NativeSelectedRounds.rounds_native : ∀ {C : Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C →
    ∀ {lp flow : List Nat → List Nat} (p : Lax263307Proofs.NativeSelectedLP.Program lp)
      (q : Lax263307Proofs.NativeSelectedNear.Program flow) (cfg : Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp p) cfg.lp →
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp p) cfg.lpWidth →
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow q) cfg.flow →
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow q) cfg.flowWidth →
              Lax263307Proofs.NativeEncodedLP.Encoded lp →
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b →
                  Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b →
                    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.K →
                      @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.b →
                        ∀ {n : Nat} (G : SimpleGraph (Fin n))
                          [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                          (D k fuel S v c R w rootN capacity childSteps childTime : Nat) (extent : String → Nat)
                          (front : List Nat),
                          Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                              capacity
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) fuel
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              n G k (@List.length Nat front) →
                            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n →
                              @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) D →
                                @LT.lt Nat instLTNat (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k →
                                  Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c →
                                    @Lax263307Proofs.NativeSelectedRounds.Bounds lp flow cfg p q n G inst D k fuel S v c
                                        R w extent front →
                                      @Lax263307Proofs.NativeRecursiveSetup.Rounds n
                                        (Lax263307Proofs.NativeSelectedRounds.level cfg n D) D k
                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                        (Lax263307.AlgorithmParameters.load cfg.b n D)
                                        (Lax263307Proofs.NativeSelectedRounds.F cfg n D) fuel S v
                                        (Lax263307Proofs.NativeSelectedRounds.limit cfg n D) w
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@Lax263307Proofs.NativeSelectedRounds.space lp flow cfg p q n D k R)
                                        (@Lax263307Proofs.NativeSelectedLP.oracleTime lp p R)
                                        (@Lax263307Proofs.NativeSelectedLP.callCost lp p R)
                                        (@Lax263307Proofs.NativeSelectedRounds.flowTime lp flow cfg p q n D k R)
                                        childSteps childTime c
                                        (Lax263307Proofs.NativeOraclePrecision.roundedHeight
                                          (@Lax263307Proofs.NativeSelectedLP.Program.width lp p) R)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@Lax263307Proofs.NativeSelectedRounds.oracleLocal lp flow cfg p q n D k R S)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            childTime))
                                        (@Lax263307Proofs.NativeSelectedRounds.roundCost lp cfg p c R) cfg G inst lp
                                        flow extent front
                                        (@Lax263307Proofs.NativeNodeExecution.child n cfg lp flow D fuel G inst)
                                        (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                            (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                          capacity) := by sorry
