-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeOracleRounds_search_segment
-- name    : Lax263307Proofs.NativeOracleRounds.search_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:55:54.112955+00:00
-- url     : https://prove2.me/theorems/0d0c30d9-6aa3-4261-b366-85e67384364e
-- title:
--   Actual bounded search from single-query and update executions
-- statement:
--   Fix a graph with $n$ vertices, a moment level, native core configuration and complete oracle-search setup. Let $L$ be the prescribed number of rounded-search steps at the specified precision. Start at phase 4 with rounded state $(1,0)$ and the complete storage and frame context. Suppose $s_c$ bounds each child execution and $t_o,t_r$ are the uniform oracle and rounded-update time bounds.
--
--   The actual phase machine executes the complete rounded search with a segment satisfying
--   $$ s\le ((s_c+5)(n+1)+7)L,\qquad t\le(t_o+t_r)L. $$
--   Its stopped answer is exactly the bounded functional search, and the full context and root frame are retained. This statement connects the finite operational search to its recursive algorithmic specification.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOracleRounds.lean, theorem search_segment

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

theorem Lax263307Proofs.NativeOracleRounds.search_segment : ∀ {n r : Nat}
  (D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime c roundH
    oracleCost roundCost precision : Nat)
  (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n))
  [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (lp flow : List Nat → List Nat)
  (extent : String → Nat) (front : List Nat)
  (child : (C : Finset (Fin n)) → Nat → Option (Finset (Fin (@Finset.card (Fin n) C)))),
  @Lax263307Proofs.NativeOracleRounds.Setup n r D k p b load F fuel S v limit w M farM nearM costH T space oracleTime
      callCost flowTime childSteps childTime c roundH oracleCost roundCost cfg G inst lp flow extent front child →
    @Eq Nat limit (Lax263307.RoundedOracleSearch.steps (Lax263307.MomentLP.dimension n r) precision) →
      ∀ (σ : Lax808846Proofs.Imp.Env),
        @Lax263307Proofs.NativeOracleContext.Context n
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
            D k r p b load F fuel S v limit cfg G inst extent front σ →
          @Lax263307Proofs.NativeRoundedTrace.StoredState (Lax263307.MomentLP.dimension n r)
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Prod.mk (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                (Fin (Lax263307.MomentLP.dimension n r) → Rat)
                (@OfNat.ofNat
                  (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                  (nat_lit 1)
                  (@One.toOfNat1
                    (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                    (@Matrix.one (Fin (Lax263307.MomentLP.dimension n r)) Rat
                      (instDecidableEqFin (Lax263307.MomentLP.dimension n r))
                      (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                      (@AddMonoidWithOne.toOne Rat
                        (@AddGroupWithOne.toAddMonoidWithOne Rat
                          (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))
                (@OfNat.ofNat (Fin (Lax263307.MomentLP.dimension n r) → Rat) (nat_lit 0)
                  (@Zero.toOfNat0 (Fin (Lax263307.MomentLP.dimension n r) → Rat)
                    (@Pi.instZero (Fin (Lax263307.MomentLP.dimension n r))
                      (fun (a : Fin (Lax263307.MomentLP.dimension n r)) => Rat)
                      fun (i : Fin (Lax263307.MomentLP.dimension n r)) =>
                      @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
              σ →
            @Eq Nat (σ.vars "machine.running") (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @Eq Nat (σ.vars "machine.phase") (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                ∃ (τ : Lax808846Proofs.Imp.Env) (transitions : Nat) (total : Nat),
                  And
                    (Lax263307Proofs.NativeMachineSegment.Segment
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                      (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ)
                    (And
                      (@LE.le Nat instLENat transitions
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) childSteps
                                (@OfNat.ofNat Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (@OfNat.ofNat Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                          limit))
                      (And
                        (@LE.le Nat instLENat total
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) oracleCost roundCost) limit))
                        (And
                          (@Lax263307Proofs.NativeOracleContext.Context n
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                            D k r p b load F fuel S v limit cfg G inst extent front τ)
                          (And
                            (@Lax263307Proofs.NativeRoundTrace.Stopped n
                              (@Lax263307.RoundedOracleSearch.search (Lax263307.MomentLP.dimension n r) (Finset (Fin n))
                                (@Lax263307Proofs.NativeOracleRounds.oracle n r lp flow G inst D k p b load F child)
                                precision)
                              τ)
                            (Lax263307Proofs.NativeOracleContext.RootData σ τ))))) := by sorry
