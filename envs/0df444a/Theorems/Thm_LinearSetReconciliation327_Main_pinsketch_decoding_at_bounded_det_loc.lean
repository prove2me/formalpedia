-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at_bounded_det_loc
-- name    : LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded_det_loc
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T09:07:32.07736+00:00
-- url     : https://prove2.me/theorems/684d13e3-7b19-4d6b-bb6a-bbb16eabf6fa
-- title:
--   Residual B: the decoder's output list lives inside the decoder's scratch (combined weakening)
-- statement:
--   **Residual B for Theorem 6.5's row stage: where the decoder's output list lives.**
--
--   Proposition 2.1's decoder exposes its output as an explicit list: the $r_1$ words starting at the
--   address in $r_0$, i.e. `outList s' = [s'.mem (r_0 + i) : i < r_1]`.  The published postcondition
--   `decoderPost` says that this list is a duplicate-free enumeration of the support of the decoded
--   vector --- but it says nothing about **where** it lives in memory.  The row stage's repack step,
--   however, needs `listBase + len <= rowSlot j` (from `RepackPre`), so it needs to know that the output
--   block of the decoder run ends inside the decoder's own scratch.  This theorem supplies exactly
--   that:
--
--   $$\exists s'.\ \mathsf{HaltsWithin}\ \ldots\ s\ s' \wedge \mathsf{decoderPost}\ s' \wedge
--   \bigl(\forall a \ge \mathsf{decoderAllocEnd}(t),\ s'.mem\, a = s.mem\, a\bigr) \wedge
--   s'.regs\, r_0 + s'.regs\, r_1 \le \mathsf{decoderAllocEnd}(t).$$
--
--   It is the combined-weakening decoder contract of `pinsketch_decoding_at_bounded_det` (bounded zero
--   hypothesis + the weakened `det`) with the location conjunct added.
--
--   The bound is *not* derivable from `decoderPost`: it comes from the machine.  The 9-instruction finish
--   block of Proposition 2.1's decoder loads $r_0 := \mathsf{decoderOutputBase}(t)$ and
--   $r_1 := (\text{root count}) \le t$ from the decoder's metadata slots, and leaves memory untouched;
--   together with $\mathsf{decoderOutputBase}(t) + t \le \mathsf{decoderAllocEnd}(t)$ this gives the
--   statement.  The formalization note records the exact construction.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Proposition 2.1 (the base-relative decoder) and Theorem 6.5 (the row loop); the project's verified development.

import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122

namespace LinearSetReconciliation327.Main

/-- **Residual B of the row stage**: Proposition 2.1's decoder at the combined weakening, *and* the
output-location bound.  Besides `decoderPost` and the frame above `decoderAllocEnd t`, the run ends
with `s'.regs r0 + s'.regs r1 ≤ decoderAllocEnd t`: the output list that the finish block exposes in
`(r0, r1)` lives inside the decoder's own scratch.  `decoderPost` alone says nothing about where the
output list lives, so `RepackPre`'s `listBase + len ≤ rowSlot j` cannot be discharged from it. -/
theorem pinsketch_decoding_at_bounded_det_loc {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
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
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) ∧
      s'.regs r0 + s'.regs r1 ≤ decoderAllocEnd t := by sorry

end LinearSetReconciliation327.Main
