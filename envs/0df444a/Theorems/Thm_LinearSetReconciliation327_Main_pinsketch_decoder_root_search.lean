-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_root_search
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_root_search
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:35:52.585062+00:00
-- url     : https://prove2.me/theorems/16fa8228-c246-47c0-a2a9-a57986a07964
-- title:
--   Pinsketch decoder, stage 3: polynomial-time root search
-- statement:
--   This is the contract of the third stage of the Pinsketch decoder: the root search.
--
--   Given a state satisfying `KeyReady` (a minimum key solution for the stored power sums), the stage executes `rootSearchProcedure` from program counter `pc` and halts within $4047$ steps. The resulting state satisfies `CandidateReady`: it contains a candidate support for the syndrome, obtained by finding the roots of the key polynomial with the trace-splitting tree and emitting their addresses into the output region. The stage modifies only the addresses in `rootSearchWritable` (the six working rows, the capacity region, the two queues and the output region), as recorded by `MemoryFrame`.
--
--   The number of steps is bounded by `rootPhaseBudget t w`, the polynomial budget of the trace-splitting recursion; the hypothesis $N < 2^{w}$ ensures that each field element's address fits in one word.
--
--   **Formalization Note** `CandidateReady` is a pure memory predicate: it says which rows and queues hold the candidate support, not that the candidate is correct. Correctness is established by the verification stage.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch decoder, root-search stage) and Appendix C; Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_root_search
    {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile rootSearchProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (hN : N < 2 ^ w) (hReady : KeyReady b E t N e m) :
    Sem P E pc (pc + 4047) (boundaryState pc m)
      (fun k z => k ≤ rootPhaseBudget t w ∧ ∃ m', z = boundaryState (pc + 4047) m' ∧
        CandidateReady b ι t N e m' ∧ MemoryFrame
          (rootSearchWritable (decoderRowBase t 0) (decoderRowBase t 6) (decoderRowBase t 1) (decoderRowBase t 7)
            (decoderRowBase t 4) (decoderCapacity t) (decoderQueue0 t) (decoderQueue1 t) (decoderOutputBase t) t) m m') := by sorry
