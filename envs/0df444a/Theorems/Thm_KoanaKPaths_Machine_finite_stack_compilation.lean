-- Prove2me | Theorems.Thm_KoanaKPaths_Machine_finite_stack_compilation
-- name    : KoanaKPaths.Machine.finite_stack_compilation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:54:20.289195+00:00
-- url     : https://prove2.me/theorems/f376864c-5dd7-4e5c-85b3-9eac055e86f6
-- title:
--   Linear simulation of charged stack executions by a fair-bit machine
-- statement:
--   Fix a finite program over $S$ work stacks, an entry address and a finite bound on every jump and return address. There is a constant $A>0$, depending only on this program, such that every execution from empty work and control stacks which takes $t$ flat steps and returns with output word $w$ is realized by one fixed fair-bit machine within
--
--   $$A\bigl(t+|w|+2\bigr)$$
--
--   steps and random bits. This holds for every deterministic input and every finite random tape. The logical input stream is the deterministic input, one fixed separator, and then the tape bits; the tape length is not supplied as an input parameter.
--
--   This simulation preserves the exponential base in the counting algorithm's runtime because its overhead is linear, with a program-dependent constant. All stack alphabets and internal registers are finite. The bit-use bound holds at every intermediate configuration, as required by the mission's RunsWithin predicate.
-- source:
--   Supporting machine refinement for Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 9 / PDF p. 10, Section 3.2 running-time argument. Operational source: platform Definitions.Def_IntMul_SS_Defs1, NLogN.Instr/fstep/Steps (charged finite-alphabet stack programs), and Mathlib 0df444a, Mathlib/Computability/TuringMachine/Computable.lean (FinTM2), StackTuringMachine.lean (TM2.stepAux). https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/StackTuringMachine.lean

import Definitions.Def_KoanaKPaths_BitStackAdapter

theorem KoanaKPaths.Machine.finite_stack_compilation (S L entry : ℕ)
    (code : ℕ → NLogN.Instr S) (he : entry < L+1)
    (hvalid : ∀ pc < L+1, NLogN.Instr.Valid (L+1) (code pc)) :
    ∃ A : ℕ, 0 < A ∧ ∀ (input tape : List Bool) (c : NLogN.Cfg S) (t : ℕ),
      NLogN.Steps (KoanaKPaths.Machine.logicalInput input tape) code
        ⟨entry,NLogN.St.init S,[]⟩ t c → code c.pc = .ret → c.ctl = [] →
      (KoanaKPaths.Machine.flatMachine L entry code).RunsWithin input tape
        (A*(t+c.σ.out.length+2)) c.σ.out := by sorry
