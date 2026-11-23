-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_ringHom_adicCompletion_under
-- name    : GlobalTheory.QNorm.exists_ringHom_adicCompletion_under
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:48.035132+00:00
-- url     : https://prove2.me/theorems/7ee31160-5883-4e76-b22d-f4ed1aa5ab04
-- title:
--   QNorm: exists ring Hom adic Completion under
-- statement:
--   The QNorm construction uses the exists ring Hom adic Completion under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRingHomAdicCompletionUnder.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRingHomAdicCompletionUnder.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletionUnder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem GlobalTheory.QNorm.exists_ringHom_adicCompletion_under :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by sorry
