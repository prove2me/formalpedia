-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_finPart_localIdele
-- name    : GlobalTheory.HeckeSplit.finPart_localIdele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:56.405175+00:00
-- url     : https://prove2.me/theorems/e7db17dc-178c-4922-b0be-aa12cdf1c2d0
-- title:
--   Hecke Split: fin Part local Idele
-- statement:
--   The Hecke Split construction uses the fin Part local Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L87-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L87-L90

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

theorem GlobalTheory.HeckeSplit.finPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.HeckeValGen.localIdele L v x) = x := by sorry
