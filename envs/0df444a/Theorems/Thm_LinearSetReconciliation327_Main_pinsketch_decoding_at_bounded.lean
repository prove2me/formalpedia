-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at_bounded
-- name    : LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T06:04:28.390034+00:00
-- url     : https://prove2.me/theorems/528da743-e0ec-4685-9549-928df635d714
-- title:
--   Proposition 2.1's decoder from a bounded zero hypothesis (Theorem 6.5 row-loop interface)
-- statement:
--   Proposition 2.1 decodes a word $y\in\mathbb{F}_2^{tw}$ from the $2t$ odd power sums of its error vector, provided the payload is staged at a word base $\beta$ of a memory that vanishes outside the payload window $[\beta,\beta+L)$ *unbounded above*, where $L=\lceil tw/(8w)\rceil$.  Theorem 6.5's row loop runs the decoder $d$ times in one memory and cannot supply that: after iteration $j$ the row-$j$ bitmap sits above Proposition 2.1's scratch and is non-zero by design.
--
--   This theorem states the same decoder at the bounded hypothesis that the row loop's own clearing pass $\mathrm{clearFull}\ 0\ \mathsf{decoderAllocEnd}(t)$ provides:
--
--   $$m=0\ \text{on}\ [L,\beta),\qquad m=0\ \text{on}\ [\beta+L,\mathsf{decoderAllocEnd}(t)),$$
--
--   with nothing assumed above $\mathsf{decoderAllocEnd}(t)=8t^2+44t+144$, together with the layout conditions $\beta+2L\le\mathsf{decoderAllocEnd}(t)$ and $\beta+2L<2^{8w}$.  The conclusion adds the row-loop frame: the run leaves every word at or above $\mathsf{decoderAllocEnd}(t)$ untouched, so the earlier rows' bitmaps survive.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, Linear Set Reconciliation with O(d) Additive Redundancy), Proposition 2.1 and Theorem 6.5

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt

namespace LinearSetReconciliation327.Main

/-- **Proposition 2.1's decoder at an arbitrary payload base, from the bounded zero hypothesis
that Theorem 6.5's row loop supplies.**  Open child: the four stage contracts at this hypothesis are
published (`pinsketch_copyin_at_bounded`, `pinsketch_decoder_readB`,
`pinsketch_decoder_key_solver_bounded`, the root search, `pinsketch_decoder_verifier_frame`); the
composition itself is not yet proved. -/
theorem pinsketch_decoding_at_bounded {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w)) :
    ∃ s', HaltsWithin (programOfStatement (pinsketchRunStmt t w β))
        (detEnv (8 * w) (detStd t N b ι))
        (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      decoderPost (N := N) b ι y s' ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) := by sorry

end LinearSetReconciliation327.Main
