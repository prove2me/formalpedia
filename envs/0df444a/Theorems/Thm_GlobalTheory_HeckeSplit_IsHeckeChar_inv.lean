-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_IsHeckeChar_inv
-- name    : GlobalTheory.HeckeSplit.IsHeckeChar.inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:57.986257+00:00
-- url     : https://prove2.me/theorems/03139f47-621d-4f4e-8f8d-933f5a8d6659
-- title:
--   Is Hecke Char: inv
-- statement:
--   The Is Hecke Char construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L116-L117

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

theorem GlobalTheory.HeckeSplit.IsHeckeChar.inv {χ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) :
    IsHeckeChar L χ⁻¹ := by sorry
