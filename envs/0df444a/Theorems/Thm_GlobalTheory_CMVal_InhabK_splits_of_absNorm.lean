-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_splits_of_absNorm
-- name    : GlobalTheory.CMVal.InhabK.splits_of_absNorm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:04:51.651872+00:00
-- url     : https://prove2.me/theorems/5ef892f8-ccdb-479d-a565-b02330f7bbaf
-- title:
--   Inhab K: splits of abs Norm
-- statement:
--   The Inhab K construction uses the splits of abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L44-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L44-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E

theorem GlobalTheory.CMVal.InhabK.splits_of_absNorm {l : ℕ} (hl : l.Prime) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E))
    (hv : Over P v) (hN : Ideal.absNorm P.asIdeal = l) (x : 𝓞 E) (hx : x - cj x ∉ P.asIdeal) : Splits v := by sorry
