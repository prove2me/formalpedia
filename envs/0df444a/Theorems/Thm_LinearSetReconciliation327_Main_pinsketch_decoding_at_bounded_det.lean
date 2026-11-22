-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at_bounded_det
-- name    : LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded_det
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T08:56:06.471045+00:00
-- url     : https://prove2.me/theorems/e37b11f4-a7a5-4d0d-9c00-51e1f42ae7a6
-- title:
--   Proposition 2.1's decoder at bounded zero and with the weakened `det` contract (combined weakening)
-- statement:
--   Proposition 2.1's decoder, run from an arbitrary payload base beta at the *bounded* zero hypothesis (m = 0 on [L, beta) and on [beta + L, decoderAllocEnd t), where L = wordsOf (8w) (tw)), with the layout conditions beta + 2L <= decoderAllocEnd t and beta + 2L < 2^(8w), halts within positiveDecoderBudget t w + 24L + 40 steps with decoderPost, and leaves every word at or above decoderAllocEnd t untouched --- in the *weakened* environment detEnv (8w) dt, where dt agrees with detStd t N b iota on the ten header slots {0,1,2,4,5,6,8,9,10,12} and on every table address >= detMulBase w.  This is exactly the combination Theorem 6.5's row body needs: the same environment carries the composite header (det 2 = R, det 3 = rowBase, det 4 = stageLen, det 12 = W, det 15 = payTab, det 16 = stageBase), while the earlier rows' bitmaps above the decoder's scratch survive the run.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.1 (the base-relative decoder), Theorem 6.5 (the row loop) and its row body; the project's verified development, whose two published weakenings (`pinsketch_decoding_at_bounded`, `pinsketch_decoding_at_det`) are combined here.

import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122

namespace LinearSetReconciliation327.Main

/-- **Proposition 2.1's decoder at the combined weakening**: the bounded zero hypothesis of
`pinsketch_decoding_at_bounded` together with the weakened `det` hypothesis of
`pinsketch_decoding_at_det`.  The run halts within the published budget with `decoderPost` and leaves
every word at or above `decoderAllocEnd t` untouched. -/
theorem pinsketch_decoding_at_bounded_det {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState) (dt : ℕ → ℕ)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w))
    (hdt : (∀ a, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
        a = 12) → dt a = detStd t N b ι a) ∧
      (∀ a, detMulBase w ≤ a → dt a = detStd t N b ι a)) :
    ∃ s', HaltsWithin (programOfStatement (pinsketchRunStmt t w β))
        (detEnv (8 * w) dt)
        (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      decoderPost (N := N) b ι y s' ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) := by sorry

end LinearSetReconciliation327.Main
