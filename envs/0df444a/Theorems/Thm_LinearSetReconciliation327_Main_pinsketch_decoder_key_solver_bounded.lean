-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver_bounded
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_key_solver_bounded
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T05:46:50.143159+00:00
-- url     : https://prove2.me/theorems/5db4fd42-28ad-4ba5-ae2d-9df2eeda733f
-- title:
--   Proposition 2.1's key-solver stage at a bounded zero hypothesis (row-loop interface)
-- statement:
--   Proposition 2.1's key solver `keySolverProcedure` takes, besides the determinant parameters and the saved syndrome, a memory that is zero above `decoderSavedBase t + 2*t`.  That hypothesis is unbounded above and is false from the second row of Theorem 6.5's row loop, where earlier rows' bitmaps sit above Proposition 2.1's scratch.  This theorem states the same stage at the bounded hypothesis `decoderSavedBase t + 2*t <= addr -> addr < decoderAllocEnd t -> m addr = 0`, which is exactly what the row loop's clearing pass `clearFull 0 (decoderAllocEnd t)` supplies: in the same cost the stage reaches a memory `m'` with `KeyReady b E t N e m'` and it moves only `solverInitWritable t`, which lies inside `[0, decoderAllocEnd t)` (`MemoryFrame (solverInitWritable t) m m'`), so the earlier rows' bitmaps survive.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.1 (the base-relative decoder) and Theorem 6.5 (the row loop); the verified development of the project (`Solutions/Sol_proposition_2_1.lean`, the accepted proof of `pinsketch_decoder_key_solver`), whose unbounded tail hypothesis is replaced here by the bounded one the row loop can supply.

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

namespace LinearSetReconciliation327.Main

theorem pinsketch_decoder_key_solver_bounded {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv) (pc : ℕ)
    (e : ℕ → F) (m : ℕ → ℕ) (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w) (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → addr < decoderAllocEnd t → m addr = 0) :
    Sem P E pc (pc + 960) (boundaryState pc m)
      (fun k z => k ≤ (34 * decoderCapacity t + (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
          12 * decoderCapacity t + 385 ∧ ∃ m', z = boundaryState (pc + 960) m' ∧
        KeyReady b E t N e m' ∧
        MemoryFrame (solverInitWritable t) m m') := by sorry

end LinearSetReconciliation327.Main
