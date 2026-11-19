-- Prove2me | Theorems.Thm_Lax759944Proofs_RamToTM_finite_sparseStep_correct
-- name    : Lax759944Proofs.RamToTM.finite_sparseStep_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:49.975552+00:00
-- url     : https://prove2.me/theorems/876272ea-11fe-4891-ba58-db2a71ddbf4a
-- title:
--   Finite tape simulation of one sparse RAM step
-- statement:
--   Fix a finite RAM program, a positive word width $w$, and an instruction-argument bound $N$. A sparse RAM state has an accumulator below $2^w$ and normalized sparse memory. Whenever one sparse RAM step takes $s$ to $s'$, every corresponding boundary configuration of the finite tape interpreter reaches the boundary configuration representing $s'$, in at most
--   $$\operatorname{finiteStepBound}(w,s_{\rm mem})$$
--   actual local tape transitions. This is a uniform simulation statement for a finite transition table.
-- source:
--   https://github.com/szymtor/RAM-TM/blob/134e398cef46599371df99f10c9007bc34ba3868/proofs/Lax759944Proofs/RamToTM/FiniteSimulation.lean, theorem finite_sparseStep_correct

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax759944Proofs.RamToTM.finite_sparseStep_correct : ∀ {p : Lax759944Proofs.Microcode.Program} {N w : ℕ} (hbound : Lax759944Proofs.RamToTM.programArgumentBound p ≤ N),
  0 < w →
    ∀ (s s' : Lax759944Proofs.RamToTM.SparseState),
      s.acc < 2 ^ w →
        Lax759944Proofs.RamToTM.SparseMemory.Normalized w s.mem →
          Lax759944Proofs.RamToTM.sparseStep w p s = Option.some s' →
            ∀ (state : Lax759944Proofs.RamToTM.FullInterpreterState N),
              Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state = Inhabited.default →
                ∃ steps ≤ Lax759944Proofs.RamToTM.finiteStepBound w s.mem,
                  ∃ (finalState : Lax759944Proofs.RamToTM.FullInterpreterState N),
                    Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get finalState =
                        Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state ∧
                      (fun
                                (x :
                                  Option
                                    (Turing.TM2.Cfg
                                      (fun (x : Lax759944Proofs.RamToTM.CoreStack) =>
                                        Lax759944Proofs.RamToTM.SparseSymbol)
                                      (Lax759944Proofs.RamToTM.FiniteInterpreterLabel p N)
                                      (Lax759944Proofs.RamToTM.FullInterpreterState N))) =>
                              x.bind
                                (Turing.TM2.step (Lax759944Proofs.RamToTM.finiteInterpreterProgram p N hbound)))^[steps]
                          (Option.some
                            (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                              (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                                (Lax759944Proofs.RamToTM.boundPC p s.pc))
                              state (Lax759944Proofs.RamToTM.coreStacks w s))) =
                        Option.some
                          (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                            (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                              (Lax759944Proofs.RamToTM.boundPC p s'.pc))
                            finalState (Lax759944Proofs.RamToTM.coreStacks w s')) := by sorry
