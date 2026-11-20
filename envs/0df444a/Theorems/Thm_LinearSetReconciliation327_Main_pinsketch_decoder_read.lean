-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_read
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:12:48.945034+00:00
-- url     : https://prove2.me/theorems/adb1c429-657a-4132-b495-aa08ecf44011
-- title:
--   Pinsketch decoder, stage 1: reading the packed syndrome and materialising its power sums
-- statement:
--   This is the contract of the first stage of the Pinsketch decoder: the packed-word reader.
--
--   The environment is standard: the word width is $E.W = 8w$ and the field-data table is $E.\mathrm{det} = \operatorname{detStd}(t,N,b,\iota)$. Starting from the canonical initial state `decoderStart (8w) y []` with program counter `base`, the reader runs the compiled code of `inputSavedProcedure` and halts within $62t+66$ steps. In the resulting boundary state:
--   1. the $2t$ field elements of `eSeq b y` are stored contiguously at address `decoderSavedBase t`;
--   2. the syndrome polynomial `syndromePoly (eSeq b y) t` is stored at the same base up to the capacity `decoderCapacity t`;
--   3. every address beyond the saved $2t$-element block is zero.
--
--   The hypotheses are the ones the stage genuinely needs: the code is installed at `base`, the word width is a multiple of eight, $1 \le w$, $N < 2^{w}$ (so $N$ fits in a word), $t \le N$, and the environment holds the standard table.
--
--   **Formalization Note** The conclusion is a `Sem` statement with an explicit step bound; `FieldArrayStored` and `PolynomialStored` are the memory-layout predicates of the decoder model, and `eSeq`/`syndromePoly` are the table-level objects that the key solver will consume.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch decoder, read stage) and Appendix C; Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_read
    {F : Type} [Field F] [Algebra (ZMod 2) F]
    (E : RAMEnv) (P : Program) (base N t w : ℕ) (y : Fin (t * w) → ZMod 2)
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (hAt : At P base (Stmt.compile inputSavedProcedure base))
    (hW : E.W = 8 * w) (hw1 : 1 ≤ w) (hNw : N < 2 ^ w) (htN : t ≤ N)
    (hdet : E.det = detStd t N b ι) :
    Sem P E base (base + 110) { decoderStart (8 * w) y [] with pc := base }
      (fun k z => k ≤ 62 * t + 66 ∧ ∃ m', z = boundaryState (base + 110) m' ∧
        FieldArrayStored b m' (decoderSavedBase t) (2 * t) (eSeq b y) ∧
        PolynomialStored b m' (decoderSavedBase t) (decoderCapacity t) (syndromePoly (eSeq b y) t) ∧
        ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m' addr = 0) := by sorry
