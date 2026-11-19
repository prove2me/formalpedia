-- Prove2me | Theorems.Thm_Lax759944Proofs_RamToTM_finite_mul_instruction
-- name    : Lax759944Proofs.RamToTM.finite_mul_instruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:43:39.539415+00:00
-- url     : https://prove2.me/theorems/c615bc9e-4855-4d3c-8ae0-60a9bb161623
-- title:
--   Finite tape simulation of a RAM multiplication instruction
-- statement:
--   Fix a finite RAM program, an instruction-argument bound, a word width $w$, and a normalized sparse memory. Suppose the fetched instruction is multiplication by an operand with value $v$. Assume $w>0$. The finite local tape interpreter executes this instruction and returns to the next fetch boundary with accumulator
--   $$a\prime=a\,v\pmod{2^w}.$$
--   The dispatch-state projection is preserved, the other encoded RAM fields are unchanged, and the number of actual local transitions is at most $\operatorname{mulInstructionBound}(w,m)+3$.
--
--   This instruction theorem is reusable in finite simulation of any RAM program. Natural division includes its zero-divisor convention.
-- source:
--   https://github.com/szymtor/RAM-TM/blob/134e398cef46599371df99f10c9007bc34ba3868/proofs/Lax759944Proofs/RamToTM/FiniteSimulation.lean, theorem finite_mul_instruction

import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces

theorem Lax759944Proofs.RamToTM.finite_mul_instruction : ∀ {p : Lax759944Proofs.Microcode.Program} {N pc w : ℕ} (hbound : Lax759944Proofs.RamToTM.programArgumentBound p ≤ N)
  (o : Lax759944Proofs.Microcode.Op),
  p[pc]? = Option.some (Lax759944Proofs.Microcode.Instr.mul o) →
    0 < w →
      ∀ (s : Lax759944Proofs.RamToTM.SparseState),
        Lax759944Proofs.RamToTM.SparseMemory.Normalized w s.mem →
          ∀ (state : Lax759944Proofs.RamToTM.FullInterpreterState N),
            ∃ steps ≤ Lax759944Proofs.RamToTM.mulInstructionBound w s.mem + 3,
              ∃ finalState,
                Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get finalState =
                    Lax759944Proofs.RamToTM.FullInterpreterState.dispatchLens.get state ∧
                  (fun x =>
                          x.bind
                            (Turing.TM2.step (Lax759944Proofs.RamToTM.finiteInterpreterProgram p N hbound)))^[steps]
                      (Option.some
                        (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                          (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch (Lax759944Proofs.RamToTM.boundPC p pc))
                          state (Lax759944Proofs.RamToTM.coreStacks w s))) =
                    Option.some
                      (Lax759944Proofs.RamToTM.finiteInterpreterCfg
                        (Lax759944Proofs.RamToTM.FiniteInterpreterLabel.fetch
                          (Lax759944Proofs.RamToTM.nextPC p (Lax759944Proofs.RamToTM.boundPC p pc)))
                        finalState
                        (Lax759944Proofs.RamToTM.coreStacks w
                          { pc := s.pc, acc := s.acc * Lax759944Proofs.RamToTM.sparseValue w o s.mem % 2 ^ w,
                            mem := s.mem, inp := s.inp, out := s.out })) := by sorry
