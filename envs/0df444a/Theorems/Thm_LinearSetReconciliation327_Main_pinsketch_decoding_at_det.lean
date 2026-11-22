-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at_det
-- name    : LinearSetReconciliation327.Main.pinsketch_decoding_at_det
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T13:34:13.062174+00:00
-- url     : https://prove2.me/theorems/bd88235c-083d-41f8-9c77-0af7a8923574
-- title:
--   Proposition 2.1's decoder with the weakened `det` contract
-- statement:
--   The **same contract as `pinsketch_decoding_at`**, with one hypothesis weakened: the deterministic
--   table no longer has to equal `detStd t N b ι` *as a whole function*.  Proposition 2.1's decoder reads
--   `det` only at
--
--   * the ten header slots `0, 1, 2, 4, 5, 6, 8, 9, 10, 12` — `paramBody` reads `0, 1, 4, 5, 6, 12`;
--     `saveHeaderCode` reads `0, 4`; `saveDestinationCode` reads `0`; `decoderMetadataAssignments`
--     reads `1, 2`; the field-table codes read `6, 8, 9, 10`; and
--   * table addresses `≥ detMulBase w = 64` (the multiplication, squaring, inversion, position and image
--     tables, addressed as `base + index`),
--
--   so it is enough that `dt` agrees with `detStd t N b ι` on those slots.  Everything else — in
--   particular slots `3`, `7`, `11` and the whole block `13 … 63` below the first table — is **free**:
--   a composite sketch can keep its own header there, which is what a block dispatcher needs when it
--   composes Proposition 2.1's decoder with other stages inside one preprocessed table.
--
--   The conclusion is unchanged: from a payload staged at word base `β` in an otherwise zero memory, the
--   copy-in / run / copy-out layer halts within `positiveDecoderBudget(t,w) + 24⌈t/8⌉ + 40` steps and
--   returns `decoderPost`, i.e. the decoding of the sparse vector from the pinning syndromes
--   `y = pin(x)`.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.2 and §2.1, Proposition 2.1 (decoding conjunct), in the base-relative form of `pinsketch_decoding_at` with the `det` hypothesis weakened to the slots the decoder reads; from the verified development `Solutions/Sol_p21_decode_at_det.lean`.

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt

namespace LinearSetReconciliation327.Main

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}

theorem pinsketch_decoding_at_det (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState) (dt : ℕ → ℕ)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzero : ∀ a, (a < β ∨ β + wordsOf (8 * w) (t * w) ≤ a) → s.mem a = 0)
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w))
    (hdt : (∀ a, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
        a = 12) → dt a = detStd t N b ι a) ∧
      (∀ a, detMulBase w ≤ a → dt a = detStd t N b ι a)) :
    ∃ s', HaltsWithin (programOfStatement (pinsketchRunStmt t w β))
        (detEnv (8 * w) dt)
        (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      decoderPost (N := N) b ι y s' := by sorry

end LinearSetReconciliation327.Main
