-- Prove2me | Theorems.Thm_GlobalTheory_UU_SchurComp_finrank_le_of_inj
-- name    : GlobalTheory.UU.SchurComp.finrank_le_of_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:23:38.153607+00:00
-- url     : https://prove2.me/theorems/03c1d58c-ca3b-4e3a-a4e3-a68a32d481f1
-- title:
--   Schur Comp: finrank le of inj
-- statement:
--   The Schur Comp construction uses the finrank le of inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L125-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProportionalField.lean#L125-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProportionalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.SchurComp

theorem GlobalTheory.UU.SchurComp.finrank_le_of_inj {F E Q : Type} [Field F] [AddCommGroup E] [Module F E] [AddCommGroup Q] [Module F Q]
    (W : Submodule F E) (f : E →ₗ[F] Q) (hf : ∀ v ∈ W, f v = 0 → v = 0) {n : ℕ} (b : Fin n → Q)
    (hb : ∀ v, f v ∈ Submodule.span F (Set.range b)) : Module.finrank F W ≤ n ∧
      (n ≤ Module.finrank F W → ∀ q ∈ Submodule.span F (Set.range b), ∃ v ∈ W, f v = q) := by sorry
