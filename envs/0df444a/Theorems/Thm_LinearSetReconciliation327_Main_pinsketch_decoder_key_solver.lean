-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_key_solver
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:17:21.681693+00:00
-- url     : https://prove2.me/theorems/ba3c65da-cb27-4680-8a56-ea4b28fca67f
-- title:
--   Pinsketch decoder, stage 2: the in-place Padé/Berlekamp–Massey key solver
-- statement:
--   This is the contract of the second stage of the Pinsketch decoder: the in-place key solver.
--
--   Starting from a boundary state in which the $2t$ saved power sums `e` are stored at `decoderSavedBase t` (and all later memory is zero), with the standard field-data table in the environment and with the table entries $0,1,2$ holding $(t,w,N)$ modulo $2^{E.W}$, the solver executes `keySolverProcedure` from program counter `pc` and halts within $960$ steps. The resulting state satisfies `KeyReady`: it contains a minimum key solution of the Padé/Berlekamp–Massey equation for the stored power sums, and the stage modifies only `solverInitWritable`, leaving every other address unchanged (`MemoryFrame`).
--
--   The bound $960$ is the precise step count of the implemented Euclidean loop (long division, degree scan and row swap); the minimality part of `KeyReady` is what allows the verifier to conclude that no lighter support exists when the later stages reject.
--
--   **Formalization Note** The hypotheses `hEnd`, `hh0`–`hh2` record that the allocation stays inside the word-addressed memory and that the parameter words hold the expected values; `h0 : ι 0 ≠ 0` is the only field-side fact the solver needs about the evaluation point.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch decoder, key-solver stage) and Appendix C.5/D.2; Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_key_solver
    {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    Sem P E pc (pc + 960) (boundaryState pc m)
      (fun k z => k ≤ (34 * decoderCapacity t + (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
          12 * decoderCapacity t + 385 ∧ ∃ m', z = boundaryState (pc + 960) m' ∧
        KeyReady b E t N e m' ∧
        MemoryFrame (solverInitWritable t) m m') := by sorry
