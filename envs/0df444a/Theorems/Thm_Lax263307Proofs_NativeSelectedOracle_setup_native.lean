-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedOracle_setup_native
-- name    : Lax263307Proofs.NativeSelectedOracle.setup_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:08.173863+00:00
-- url     : https://prove2.me/theorems/1eac53c4-0960-45c9-aec6-9c175164aee6
-- title:
--   Construct the complete setup for one native oracle round
-- statement:
--   Fix a hereditary graph class and selected native LP and separator programs, whose code and width polynomials agree with the fixed machine configuration. Let $G$ be an eligible large node, and let its rational ellipsoid center have the stated height bound. Assume positive floor denominator, accuracy denominator at least four, the complete root resource and host bounds, and all projection, near-oracle and workspace guards. These data construct the entire setup contract for the round:
--   $$\operatorname{Setup}(G,\operatorname{state},\operatorname{selectedPrograms},\operatorname{childBounds}).$$
--   The setup retains the exact smaller-fuel child specification and supplies the operational preconditions for both projection and near-separator phases.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedOracle.lean, theorem Lax263307Proofs.NativeSelectedOracle.setup, line 25

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeSelectedOracle
end Lax263307Proofs.NativeSelectedOracle

theorem Lax263307Proofs.NativeSelectedOracle.setup_native : ∀ {C : Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C →
    ∀ {lp flow : List Nat → List Nat} (lpProgram : Lax263307Proofs.NativeSelectedLP.Program lp)
      (flowProgram : Lax263307Proofs.NativeSelectedNear.Program flow) (cfg : Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp lpProgram) cfg.lp →
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp lpProgram) cfg.lpWidth →
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow flowProgram) cfg.flow →
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow flowProgram) cfg.flowWidth →
              Lax263307Proofs.NativeEncodedLP.Encoded lp →
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b →
                  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.K →
                    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.b →
                      ∀ {n : Nat} (G : SimpleGraph (Fin n))
                        [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                        (D k fuel S v R F w rootN capacity childSteps childTime : Nat) (extent : String → Nat)
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
                              @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
                                @LT.lt Nat instLTNat (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k →
                                  @LE.le Nat instLENat n R →
                                    @LE.le Nat instLENat k R →
                                      @LE.le Nat instLENat (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                          R →
                                        @LE.le Nat instLENat D R →
                                          @LE.le Nat instLENat F R →
                                            @LE.le Nat instLENat
                                                (Lax263307.MomentLP.dimension n
                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                                                R →
                                              ∀
                                                (state :
                                                  Lax263307.RoundedOracleSearch.State
                                                    (Lax263307.MomentLP.dimension n
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                (∀
                                                    (i :
                                                      Fin
                                                        (Lax263307.MomentLP.dimension n
                                                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                    Lax263307.NativeRoundedStep.height
                                                      (@Prod.snd
                                                        (Matrix
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          Rat)
                                                        (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)) →
                                                          Rat)
                                                        state i)
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                        (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                                  @Lax263307Proofs.NativeOracleExecution.ProjectionBounds n D k
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) F
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@OfNat.ofNat Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                      w (@Lax263307Proofs.NativeSelectedLP.oracleTime lp lpProgram R) G
                                                      inst extent →
                                                    Lax263307Proofs.NativeNearExecution.Bounds n
                                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                                        (@HPow.hPow Nat Nat Nat
                                                          (@instHPow Nat Nat
                                                            (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        fuel S w cfg extent front →
                                                      @LE.le Nat instLENat
                                                          (@Lax263307Proofs.NativeSelectedLP.wordHeight lp lpProgram R)
                                                          w →
                                                        @LE.le Nat instLENat
                                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                              (Lax263307Proofs.NativeCutResources.wordExponent
                                                                (Lax263307.MomentLP.dimension n
                                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b
                                                                    n D))
                                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                    (@OfNat.ofNat Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                      lp lpProgram R))
                                                                  (@OfNat.ofNat Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                                            w →
                                                          @LT.lt Nat instLTNat
                                                              (Lax263307Proofs.NativeSelectedLP.queryBound R)
                                                              (extent "vm.input") →
                                                            @LE.le Nat instLENat
                                                                (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                                                  (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                    cfg.b n
                                                                    (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R)))
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.code flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.width
                                                                    flow flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.time flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.output
                                                                    flow flowProgram))
                                                                w →
                                                              (∀ (a : String),
                                                                  @Membership.mem String (List String)
                                                                      (@List.instMembership String)
                                                                      Lax263307Proofs.NativeSeparatorContext.workspace
                                                                      a →
                                                                    @LE.le Nat instLENat
                                                                      (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                        (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                          cfg.b n
                                                                          (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                          k
                                                                          (@HMul.hMul Nat Nat Nat
                                                                            (@instHMul Nat instMulNat)
                                                                            (@OfNat.ofNat Nat (nat_lit 2)
                                                                              (instOfNatNat (nat_lit 2)))
                                                                            (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                              lp lpProgram R)))
                                                                        (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                          flow flowProgram))
                                                                      (extent a)) →
                                                                ∀
                                                                  (child :
                                                                    (A : Finset (Fin n)) →
                                                                      Nat →
                                                                        Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                                                  @Lax263307Proofs.NativeRecursiveSetup.Oracle n
                                                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    D k
                                                                    (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    cfg.b (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                    F fuel S v w
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                        (@OfNat.ofNat Nat (nat_lit 100)
                                                                          (instOfNatNat (nat_lit 100)))
                                                                        (@HAdd.hAdd Nat Nat Nat
                                                                          (@instHAdd Nat instAddNat) R
                                                                          (@OfNat.ofNat Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1))))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          (@OfNat.ofNat Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R))
                                                                        (@OfNat.ofNat Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1)))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                      (@OfNat.ofNat Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) R
                                                                      (@OfNat.ofNat Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))
                                                                    (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          (@OfNat.ofNat Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    (@Lax263307Proofs.NativeSelectedLP.oracleTime lp
                                                                      lpProgram R)
                                                                    (@Lax263307Proofs.NativeSelectedLP.callCost lp
                                                                      lpProgram R)
                                                                    (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          (@OfNat.ofNat Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.code
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.coeff
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    childSteps childTime cfg G inst lp flow extent front
                                                                    child state
                                                                    (Lax263307Proofs.NativeRecursiveDomain.eligible C
                                                                      rootN
                                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat) S
                                                                          (@List.length String
                                                                            (Lax263307Proofs.NativeCoreMachine.frameArrays
                                                                              cfg)))
                                                                        (@List.length String
                                                                          (Lax263307Proofs.NativeCoreMachine.frameScalars
                                                                            cfg)))
                                                                      capacity) := by sorry
