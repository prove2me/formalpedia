-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDVR_exists_complete
-- name    : GlobalTheory.CompleteDVR.exists_complete
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:33.270771+00:00
-- url     : https://prove2.me/theorems/005bc541-c28e-4001-b4b4-04e3f70805f3
-- title:
--   Complete DVR: exists complete
-- statement:
--   The Complete DVR construction uses the exists complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L47-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L47-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR

theorem GlobalTheory.CompleteDVR.exists_complete : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V],
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by sorry
