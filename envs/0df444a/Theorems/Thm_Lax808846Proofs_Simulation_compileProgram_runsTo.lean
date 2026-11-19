-- Prove2me | Theorems.Thm_Lax808846Proofs_Simulation_compileProgram_runsTo
-- name    : Lax808846Proofs.Simulation.compileProgram_runsTo
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:17:11.911616+00:00
-- url     : https://prove2.me/theorems/78f4a8be-6d33-4a67-b065-e40e6171f876
-- title:
--   Correct compilation of bounded structured commands
-- statement:
--   Let $c$ be a structured command, $L$ a compatible finite memory layout, and $B,w$ bounds with enough word space for that layout. If all input words are below $B$ and the bounded operational semantics executes $c$ in $k$ steps, its fixed compiled RAM program returns the same output in a time $t$ satisfying
--   $$t\le L_{\rm const}k+1.$$
--   This gives a semantic and quantitative compiler interface, starting from standard zero RAM memory.
-- source:
--   https://github.com/lax-archive/lax-submissions/blob/9394e531cc51cb67a0214bca3f9264dfe97ba5c7/word-ram/proofs/Lax808846Proofs/Simulation.lean, theorem compileProgram_runsTo

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax808846Proofs.Simulation.compileProgram_runsTo : ∀ {L : Lax808846Proofs.Compile.Layout} {B w : ℕ} {c : Lax808846Proofs.Imp.Com} {ext : String → ℕ} {x : List ℕ}
  {σ' : Lax808846Proofs.Imp.Env} {k : ℕ},
  L.FitsWords B w →
    Lax808846Proofs.Compile.Com.Ok L c →
      (∀ v ∈ x, v < B) →
        Lax808846Proofs.Imp.BigStepB B c (Lax808846Proofs.Imp.initEnv ext x) σ' k →
          ∃ t ≤ L.const * k + 1, Lax808846.Ram.RunsTo w (Lax808846Proofs.Compile.compileProgram L c) x σ'.out t := by sorry
