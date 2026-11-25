-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_TrivAt_unrAt
-- name    : GlobalTheory.HeckeSplit.TrivAt.unrAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:56.028196+00:00
-- url     : https://prove2.me/theorems/e38ebd6a-5d3d-4926-9737-45c29f5b6092
-- title:
--   Triv At: unr At
-- statement:
--   The Triv At construction uses the unr At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L119-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeSplit
open NumberField IsDedekindDomain HeckeValGen
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)
variable {L}

theorem GlobalTheory.HeckeSplit.TrivAt.unrAt {χ : Ideles L →* ℂˣ} {v : HeightOneSpectrum (𝓞 L)} (h : TrivAt χ v) :
    UnrAt χ v := by sorry
