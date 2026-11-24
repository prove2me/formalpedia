-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_IsHeckeChar_mul
-- name    : GlobalTheory.HeckeSplit.IsHeckeChar.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:11.463892+00:00
-- url     : https://prove2.me/theorems/7f2bfda4-a817-4d78-8c85-7bc59083e452
-- title:
--   Is Hecke Char: mul
-- statement:
--   The Is Hecke Char construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L113-L114

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

theorem GlobalTheory.HeckeSplit.IsHeckeChar.mul {χ ψ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) (hψ : IsHeckeChar L ψ) :
    IsHeckeChar L (χ * ψ) := by sorry
