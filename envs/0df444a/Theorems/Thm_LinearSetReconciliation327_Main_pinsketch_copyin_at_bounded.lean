-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_copyin_at_bounded
-- name    : LinearSetReconciliation327.Main.pinsketch_copyin_at_bounded
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T03:12:46.173831+00:00
-- url     : https://prove2.me/theorems/3961732f-a462-48ab-b33f-5b22ca713d43
-- title:
--   Proposition 2.1's copy-in at a bounded zero hypothesis (row-loop interface)
-- statement:
--   Proposition 2.1's base-relative decoder `pinsketchRunStmt t w beta` copies the payload of `y` from the word base `beta` down to `0`, erases the source block with the zero shadow block, zeroes the registers and loads `r1 := L`.  The published contract `pinsketch_decoding_at` requires the whole memory outside the payload window `[beta, beta+L)` to be zero, *unbounded above*; that hypothesis fails from the second row of Theorem 6.5's row loop on, because the earlier rows' bitmaps sit above 2.1's scratch and are non-zero by design.  This theorem relaxes the hypothesis to the decoder's own workspace: the memory only has to vanish on `[L, beta)` and on `[beta+L, decoderAllocEnd t)`, while everything at or above `decoderAllocEnd t` may be arbitrary.  Under that hypothesis plus `beta + 2*L <= decoderAllocEnd t` the two copy passes still produce 2.1's canonical entry state *on the workspace* --- `hintMem` on `[0, decoderAllocEnd t)` --- in at most `24*L + 39` steps, and they leave every word at or above `decoderAllocEnd t` untouched (a `MemoryFrame`).  So the copy-in composes with the row loop's clearing pass and preserves the earlier rows' bitmaps.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.1 (the base-relative decoder) and Theorem 6.5 (the row loop). Extracted from the verified development `Solutions/Sol_p21_decode_at.lean`, which proves `pinsketch_decoding_at`; here its unbounded zero hypothesis is replaced by the bounded one that the row loop can supply.

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt

namespace LinearSetReconciliation327.Main

theorem pinsketch_copyin_at_bounded {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (P : Program) (E : RAMEnv) (pc β : ℕ) (s : RAMState)
    (hAt : At P pc (Stmt.compile (pinsketchRunStmt t w β) pc))
    (hpc : s.pc = pc)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (hW : E.W = 8 * w)
    (hdet : E.det = detStd t N b ι)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ E.W)
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ E.W) :
    Sem P E pc (pc + 59) s
      (fun k z => k ≤ 24 * wordsOf (8 * w) (t * w) + 39 ∧ z.pc = pc + 59 ∧
        z.regs = layerDecoderRegs (wordsOf (8 * w) (t * w)) ∧
        (∀ a, a < decoderAllocEnd t → z.mem a = hintMem (8 * w) y [] a) ∧
        (∀ a, decoderAllocEnd t ≤ a → z.mem a = s.mem a)) := by sorry

end LinearSetReconciliation327.Main
