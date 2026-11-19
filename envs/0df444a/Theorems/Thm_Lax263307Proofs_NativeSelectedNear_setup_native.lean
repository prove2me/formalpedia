-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeSelectedNear_setup_native
-- name    : Lax263307Proofs.NativeSelectedNear.setup_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:33:40.65646+00:00
-- url     : https://prove2.me/theorems/14c74d2f-8f3f-4288-8d04-e730ecfefc63
-- title:
--   Near-branch setup from a selected flow program
-- statement:
--   Fix a hereditary graph class, the algorithm configuration and a selected deterministic flow program with its operational contract. Let an eligible recursive node have more than one vertex, accuracy denominator at least four and target larger than the direct cutoff. Suppose a rational feasible moment vector has coordinate height at most $2^H$, and the stated near-branch workspace, word width and target bounds hold. Then
--   $$\operatorname{NearSetup}(G,x,\mathrm{cfg})$$
--   holds with the declared separator runtime and recursive child domain. The conclusion supplies all conditioning, separator invocation and hereditary child guarantees required by the actual near-branch execution.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedNear.lean#L46

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax263307Proofs.NativeSelectedNear
end Lax263307Proofs.NativeSelectedNear

theorem Lax263307Proofs.NativeSelectedNear.setup_native : ∀ {C : Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C →
    ∀ {flow : List Nat → List Nat} (fp : Lax263307Proofs.NativeSelectedNear.Program flow)
      (cfg : Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp) cfg.flow →
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp) cfg.flowWidth →
          Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b →
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.K →
              @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) cfg.b →
                ∀ {n : Nat} (G : SimpleGraph (Fin n))
                  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                  (D k fuel S v H T w rootN capacity childSteps childTime : Nat) (extent : String → Nat)
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
                          ∀
                            (x :
                              Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)) →
                                Rat),
                            @Lax263307.LinearRelaxation.IsFeasible n G k
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                (@Lax263307.RationalConditioning.realVector n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                  (@Lax263307.MomentLP.decode Rat n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) x)) →
                              (∀
                                  (i :
                                    Fin
                                      (Lax263307.MomentLP.dimension n
                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                                    (x i)) →
                                @LE.le Nat instLENat
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    T →
                                  Lax263307Proofs.NativeNearExecution.Bounds n
                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                      (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                                      T fuel S w cfg extent front →
                                    @LE.le Nat instLENat
                                        (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                          (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H))
                                          (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.width flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.output flow fp))
                                        w →
                                      (∀ (a : String),
                                          @Membership.mem String (List String) (@List.instMembership String)
                                              Lax263307Proofs.NativeSeparatorContext.workspace a →
                                            @LE.le Nat instLENat
                                              (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                  (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H))
                                                (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                              (extent a)) →
                                        ∀
                                          (child :
                                            (A : Finset (Fin n)) →
                                              Nat → Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                          @Lax263307Proofs.NativeRecursiveSetup.Near n
                                            (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                            (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) fuel S v
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                                            T w
                                            (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            childSteps childTime cfg G inst flow x extent front child
                                            (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                                                  (@List.length String
                                                    (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                (@List.length String
                                                  (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                              capacity) := by sorry
