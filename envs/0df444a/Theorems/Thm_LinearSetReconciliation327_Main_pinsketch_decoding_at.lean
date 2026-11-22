-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at
-- name    : LinearSetReconciliation327.Main.pinsketch_decoding_at
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T09:37:12.952125+00:00
-- url     : https://prove2.me/theorems/19915f16-22fd-4377-b2e0-80c43a7a8a9f
-- title:
--   Proposition 2.1's decoder at an arbitrary payload base
-- statement:
--   If the payload of a $t \times w$ syndrome $y$ is staged at word base $\beta$ in an otherwise zero memory, then Proposition 2.1's decoder — run through the copy-in/run/copy-out layer — halts within $\mathrm{positiveDecoderBudget}(t,w) + 24\lceil t/8\rceil + 40$ steps and outputs the decoding of the sparse vector $x$ from the pinning syndromes $y = \mathrm{pin}(x)$: a **base-relative** form of Proposition 2.1's decoding conjunct, in which the payload sits at an arbitrary word address rather than at word $0$.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §2.2 (pinsketch syndromes and the decoder) and §2.1 (word-RAM model), Proposition 2.1 (decoding conjunct); extracted from the verified development `Solutions/Sol_p21_copyrun.lean`.

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt

namespace LinearSetReconciliation327.Main

variable {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}

theorem pinsketch_decoding_at (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzero : ∀ a, (a < β ∨ β + wordsOf (8 * w) (t * w) ≤ a) → s.mem a = 0)
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w)) :
    ∃ s', HaltsWithin (programOfStatement (pinsketchRunStmt t w β))
        (detEnv (8 * w) (detStd t N b ι))
        (((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      decoderPost (N := N) b ι y s' := by sorry

end LinearSetReconciliation327.Main
