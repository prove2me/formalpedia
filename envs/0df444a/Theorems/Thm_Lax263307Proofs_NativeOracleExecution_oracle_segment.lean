-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeOracleExecution_oracle_segment
-- name    : Lax263307Proofs.NativeOracleExecution.oracle_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:56:01.616938+00:00
-- url     : https://prove2.me/theorems/01016bb9-7931-4183-aa36-b81e1b69cfb7
-- title:
--   Complete native execution of one rounded-oracle query
-- statement:
--   Fix a graph, native core configuration, LP and flow functions, and rounded state at iteration $j$. Assume the complete published context, projection bounds, source-query storage, exact projection-call specification, far-cut bounds, and near-branch setup including bounded child executions.
--
--   Starting at phase 4 with the machine running, the actual phase machine performs one complete oracle query and reaches its reply state. The segment has at most
--   $$ (s_c+5)(n+1)+6 $$
--   transitions, where $s_c$ bounds a child execution. Its time is at most the explicit sum of the projection preparation and call, cut processing, near-execution bound and administrative constants stated in the formal interface. The resulting reply is the functional oracle reply; the rounded state, complete context and root frame are preserved. This gives the concrete single-query step used in the bounded search.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOracleExecution.lean, theorem oracle_segment

import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

theorem Lax263307Proofs.NativeOracleExecution.oracle_segment : ∀ {n r : ℕ}
  (D k p b load F fuel S v limit w M farM nearM h T space oracleTime callCost flowTime childSteps childTime : ℕ)
  (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj]
  (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
  (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) (j : ℕ)
  (state : Lax263307.RoundedOracleSearch.State (Lax263307.MomentLP.dimension n r)),
  Lax263307Proofs.NativeOracleExecution.ProjectionBounds D k r F M w oracleTime G extent →
    (∀ (i : Fin (Lax263307.MomentLP.dimension n r)), Lax263307Proofs.NativeSignedArithmetic.Bounded M (state.2 i)) →
      (Lax109476.RationalEncoding.encodeProgram
              (Lax263307.DistanceProjection.distanceProgram (Lax263307.MomentLP.program G k r)
                (Lax263307.ProjectedOracle.raw state.2))).length <
          extent "vm.input" →
        Lax808846Proofs.Reasoning.Spec (2 ^ w)
            (Lax263307Proofs.NativeProjectionTrace.InvocationInput (Lax263307.MomentLP.program G k r)
              (Lax263307.ProjectedOracle.raw state.2) (Lax263307Proofs.NativeNodeTolerance.tolerance n D F) oracleTime)
            (Lax263307Proofs.NativeProjectionOracle.command cfg.lp cfg.lpWidth)
            (fun (x τ : Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeProjectionResult.Output
                  (Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2) τ ∧
                τ.vars "projection.n" = Lax263307.MomentLP.dimension n r)
            callCost →
          (∀ (a : Fin (Lax263307.MomentLP.dimension n r) → ℚ) (β : ℚ),
              Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2 =
                  Lax263307.RationalProjection.Outcome.far a β →
                (∀ (i : Fin (Lax263307.MomentLP.dimension n r)),
                    Lax263307Proofs.NativeSignedArithmetic.Bounded farM (a i)) ∧
                  farM * Lax263307.RationalCutBuffer.denominator a + farM + Lax263307.RationalCutBuffer.denominator a +
                        3 * Lax263307.MomentLP.dimension n r +
                      23 <
                    2 ^ w) →
            (∀ (x : Fin (Lax263307.MomentLP.dimension n r) → ℚ),
                Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2 =
                    Lax263307.RationalProjection.Outcome.near x →
                  Lax263307Proofs.NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps
                    childTime cfg G flow x extent front child) →
              ∀ (σ : Lax808846Proofs.Imp.Env),
                Lax263307Proofs.NativeOracleContext.Context (2 ^ w) D k r p b load F fuel S v limit cfg G extent front
                    σ →
                  Lax263307Proofs.NativeRoundedTrace.StoredState j state σ →
                    σ.vars "machine.running" = 1 →
                      σ.vars "machine.phase" = 4 →
                        ∃ (τ : Lax808846Proofs.Imp.Env) (transitions : ℕ) (total : ℕ),
                          Lax263307Proofs.NativeMachineSegment.Segment (2 ^ w)
                              (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ ∧
                            transitions ≤ (childSteps + 5) * (n + 1) + 6 ∧
                              total ≤
                                  16 *
                                                    (Lax109476.RationalEncoding.encodeProgram
                                                        (Lax263307.MomentLP.program G k r)).length +
                                                  (36 * M.size + 124) * Lax263307.MomentLP.dimension n r +
                                                135 +
                                              callCost +
                                            2 +
                                          14 +
                                        (193 * Lax263307.MomentLP.dimension n r + 48) +
                                      Lax263307Proofs.NativeNearExecution.timeBound cfg n r nearM S h childTime
                                        flowTime +
                                    6 ∧
                                Lax263307Proofs.NativeOracleContext.Context (2 ^ w) D k r p b load F fuel S v limit cfg
                                    G extent front τ ∧
                                  Lax263307Proofs.NativeRoundedTrace.StoredState j state τ ∧
                                    Lax263307Proofs.NativeOracleExecution.Output
                                        (Lax263307Proofs.NativeOracleExecution.reply flow G D k p b load child
                                          (Lax263307Proofs.NativeOracleExecution.projection lp G k D F state.2))
                                        τ ∧
                                      Lax263307Proofs.NativeOracleContext.RootData σ τ := by sorry
