-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_unrAt_iff
-- name    : GlobalTheory.HeckeSplit.unrAt_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:50.075738+00:00
-- url     : https://prove2.me/theorems/f2f8b230-3f01-4f2b-b65f-0b423cc04628
-- title:
--   Hecke Split: unr At iff
-- statement:
--   The Hecke Split construction uses the unr At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L46-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_UnipotentAdelicQuotients_FinOrdValGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Theorems.Thm_Formalism_L2_Host_HChar_unrAt_iff

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
open NumberField IsDedekindDomain
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)

theorem GlobalTheory.HeckeSplit.unrAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.UnrAt χ.1 v ↔ χ.UnrAt v := by sorry
