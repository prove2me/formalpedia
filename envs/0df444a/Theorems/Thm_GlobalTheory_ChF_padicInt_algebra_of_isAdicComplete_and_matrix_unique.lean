-- Prove2me | Theorems.Thm_GlobalTheory_ChF_padicInt_algebra_of_isAdicComplete_and_matrix_unique
-- name    : GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:51.953077+00:00
-- url     : https://prove2.me/theorems/6831b727-4798-4748-8232-8ceb327fc990
-- title:
--   Ch F: padic Int algebra of is Adic Complete and matrix unique
-- statement:
--   The Ch F construction uses the padic Int algebra of is Adic Complete and matrix unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicIntAlgebraOfIsAdicCompleteMatrixUnique.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PadicIntAlgebraOfIsAdicCompleteMatrixUnique.lean#L38-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF

theorem GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O],
      Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ)
        (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]),
        f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by sorry
