-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCoreExecution_command_spec
-- name    : Lax263307Proofs.NativeCoreExecution.command_spec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:00.06243+00:00
-- url     : https://prove2.me/theorems/cf49f9fb-6847-437c-89d1-2175214fee77
-- title:
--   Operational correctness of the native recursive independent-set core
-- statement:
--   Fix the core configuration and uniform resource invariants for its LP and flow backends. For a graph $G$ and valid initialized recursive state, assume the eligibility, workspace and word-width bounds. The fixed core command terminates and returns the answer of the specified recursive target search. Writing $N_S,N_T$ for the recursive work bounds, its operational clock is
--   $$((N_T+26+68(N_S+3))n+98).$$
--   The conclusion includes the full root protocol and answer representation.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCoreExecution.lean, theorem command_spec

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax263307Proofs.NativeCoreExecution.command_spec : ∀ {n : ℕ} (D fuel S v w localSteps localTime branches : ℕ) (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (G : SimpleGraph (Fin n)) [inst : DecidableRel G.Adj] (lp flow : List ℕ → List ℕ) (extent : String → ℕ)
  (eligible : Lax263307Proofs.NativeNodeProtocol.Eligible)
  (resources :
    Lax263307Proofs.NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible),
  (∀ (k : ℕ), 0 < k → k ≤ n → eligible fuel n G k 0) →
    S * (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length +
                (Lax263307Proofs.NativeCoreMachine.frameScalars cfg).length +
              S +
            (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length +
          10 <
        2 ^ w →
      n + fuel + 20 < 2 ^ w →
        2 ^ n < 2 ^ w →
          have NS := Lax263307Proofs.NativeRecursionBudget.work localSteps branches fuel;
          have NT := Lax263307Proofs.NativeRecursionBudget.work localTime branches fuel;
          Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax263307Proofs.NativeCoreExecution.Input (2 ^ w) D fuel S v G extent)
            (Lax263307Proofs.NativeCoreMachine.command cfg)
            (fun (x τ : Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeCoreExecution.Root (2 ^ w) D S v cfg G extent τ ∧
                Lax263307Proofs.NativeRootTrace.Answer
                  (Lax263307.TargetSearch.search
                    (Lax263307.RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) n)
                  τ)
            ((NT + 26 + 68 * (NS + 3)) * n + 98) := by sorry
