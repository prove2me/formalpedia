-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeUnweightedExecution_command_spec_native
-- name    : Lax263307Proofs.NativeUnweightedExecution.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:25:59.881455+00:00
-- url     : https://prove2.me/theorems/f6b801f9-7b16-490a-b2bf-92b955790bbb
-- title:
--   Complete execution of the native unweighted recursive program
-- statement:
--   Fix a hereditary graph class, selected native LP and separator programs with their encoding and correctness contracts, a recursive oracle, and the source's fixed configuration. Let $G$ be a nonempty member of the class. Assume the published root accuracy, uniform resource envelope, selected budget, host-width and rounded-update program bounds. From the full initialized root state, the fixed native program terminates within its explicit cost and returns precisely the answer of the functional recursion:
--   $$\operatorname{answer}_{\rm native}=\operatorname{solve}_{\rm functional}(G).$$
--   It retains the root invariant, original order, blow-up owner data and prior output. Every recursive execution and solver call is discharged by the selected programs and numerical bounds.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeUnweightedExecution.lean, theorem Lax263307Proofs.NativeUnweightedExecution.command_spec, line 37

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax263307Proofs.NativeUnweightedExecution
end Lax263307Proofs.NativeUnweightedExecution

theorem Lax263307Proofs.NativeUnweightedExecution.command_spec_native : ∀ {C : Lax263307.GraphClasses.GraphClass},
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
                          [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
                          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                              (@Set.instMembership (SimpleGraph (Fin n))) (C n) G →
                            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                              ∀ (D c originalN R W w : Nat),
                                @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) D →
                                  @LE.le Nat instLENat n R →
                                    Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c →
                                      (∀ (m : Nat),
                                          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              m →
                                            @LE.le Nat instLENat m n →
                                              @LE.le Nat instLENat
                                                (Lax263307.ParameterResources.resource cfg.a cfg.K cfg.b m D) R) →
                                        @LE.le Nat instLENat
                                            (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R) W →
                                          @LE.le Nat instLENat (Lax263307Proofs.NativeRootWorkspace.hostHeight cfg W)
                                              w →
                                            Lax808846Proofs.Reasoning.Spec
                                              (@HPow.hPow Nat Nat Nat
                                                (@instHPow Nat Nat
                                                  (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                              (@Lax263307Proofs.NativeCoreExecution.Input n
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                                D (Lax263307.RecursionDepth.depth n)
                                                (Lax263307Proofs.NativeRootWorkspace.stride W) W G inst
                                                (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN))
                                              (Lax263307Proofs.NativeCoreMachine.command cfg)
                                              (fun (σ τ : Lax808846Proofs.Imp.Env) =>
                                                And
                                                  (@Lax263307Proofs.NativeCoreExecution.Root n
                                                    (@HPow.hPow Nat Nat Nat
                                                      (@instHPow Nat Nat
                                                        (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                                    D (Lax263307Proofs.NativeRootWorkspace.stride W) W cfg G inst
                                                    (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN) τ)
                                                  (And
                                                    (@Lax263307Proofs.NativeRootTrace.Answer n
                                                      (@Lax263307.RecursiveAlgorithm.solve n lp flow cfg.a cfg.K cfg.b D
                                                        G inst)
                                                      τ)
                                                    (And (@Eq Nat (τ.vars "input.n") (σ.vars "input.n"))
                                                      (And (@Eq Nat (τ.vars "blowup.length") (σ.vars "blowup.length"))
                                                        (And
                                                          (@Eq (List Nat) (τ.arrs "blowup.owner")
                                                            (σ.arrs "blowup.owner"))
                                                          (@Eq (List Nat) τ.out σ.out))))))
                                              (Lax263307Proofs.NativeUnweightedExecution.cost cfg n W) := by sorry
