-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeNodeExecution_large_segment
-- name    : Lax263307Proofs.NativeNodeExecution.large_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T12:30:51.010905+00:00
-- url     : https://prove2.me/theorems/e62b6e24-7e0a-4cc0-952e-b1b5b40037ba
-- title:
--   Complete large-node execution from bounded child executions
-- statement:
--   Fix a native recursive core configuration and a graph node with order $n$ and target $k$. Assume $k\le n$, the node is outside the small/exhaustive case, and its fuel is $f+1$. Let $w$ be the host word width, $D$ the precision denominator, $S$ the frame stride and $v$ the virtual word width. Suppose the published local numeric bounds and large-search resource data hold. Assume every eligible child at fuel $f$ has its required execution, with at most $s_c$ steps and time $t_c$.
--
--   Starting from the phase-1 node input, the actual core machine executes a complete large-node segment, including the child calls and return protocol. If $s_0,t_0,b$ are the local step, local time and branching bounds, then
--   $$s\le s_0+b s_c,\qquad t\le t_0+b t_c.$$
--   The returned answer is the recursive large-node attempt; the node protocol, saved parent frame and graph encoding are preserved as required by the execution interface. This is the inductive composition step used to prove the complete recursive execution theorem.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeNodeExecution.lean, theorem large_segment (lines 100–157)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces

theorem Lax263307Proofs.NativeNodeExecution.large_segment : ∀ {n : ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches : ℕ)
  (cfg : Lax263307Proofs.NativeCoreMachine.Config) (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj]
  (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
  (eligible : Lax263307Proofs.NativeNodeProtocol.Eligible),
  Lax263307Proofs.NativeNodeExecution.Bounds w D k (fuel + 1) n cfg extent →
    ∀
      (data :
        Lax263307Proofs.NativeNodeExecution.Search D k fuel S v w childSteps childTime localSteps localTime branches cfg
          G lp flow extent front eligible),
      Lax263307Proofs.NativeNodeProtocol.Children (2 ^ w) D fuel S v childSteps childTime cfg G extent front eligible
          (Lax263307Proofs.NativeNodeExecution.child cfg lp flow D fuel G) →
        ¬(k ≤ Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D ∨ n ≤ 1) →
          k ≤ n →
            ∀ (σ : Lax808846Proofs.Imp.Env),
              Lax263307Proofs.NativeNodeProtocol.Input (2 ^ w) D (fuel + 1) S v cfg G k extent front σ →
                σ.vars "machine.running" = 1 →
                  σ.vars "machine.phase" = 1 →
                    ∃ (τ : Lax808846Proofs.Imp.Env) (s : ℕ) (t : ℕ),
                      Lax263307Proofs.NativeMachineSegment.Segment (2 ^ w)
                          (Lax263307Proofs.NativeCoreMachine.phases cfg) s t σ τ ∧
                        s ≤ localSteps + branches * childSteps ∧
                          t ≤ localTime + branches * childTime ∧
                            Lax263307Proofs.NativeRoundTrace.Stopped
                                (Lax263307.RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel + 1) G k) τ ∧
                              Lax263307Proofs.NativeOracleContext.Protocol (2 ^ w) D S v cfg extent front τ ∧
                                Lax263307Proofs.NativeOracleContext.RootData σ τ ∧
                                  Lax263307Proofs.NativeNodeProtocol.GraphData G τ := by sorry
