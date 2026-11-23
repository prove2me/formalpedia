-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_infPart_localIdele
-- name    : GlobalTheory.HeckeSplit.infPart_localIdele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:39.454579+00:00
-- url     : https://prove2.me/theorems/cf226016-50df-42f2-9300-0a0b1267d48b
-- title:
--   Hecke Split: inf Part local Idele
-- statement:
--   The Hecke Split construction uses the inf Part local Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L97-L100

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
open NumberField IsDedekindDomain
variable (L : Type) [Field L] [NumberField L]
variable {L}
variable (L)

theorem GlobalTheory.HeckeSplit.infPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.HeckeValGen.localIdele L v x) = 1 := by sorry
