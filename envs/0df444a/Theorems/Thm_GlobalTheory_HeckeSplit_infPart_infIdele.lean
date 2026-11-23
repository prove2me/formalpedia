-- Prove2me | Theorems.Thm_GlobalTheory_HeckeSplit_infPart_infIdele
-- name    : GlobalTheory.HeckeSplit.infPart_infIdele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:32.588475+00:00
-- url     : https://prove2.me/theorems/06dbe23b-56ea-460e-9779-3d8771a2fc84
-- title:
--   Hecke Split: inf Part inf Idele
-- statement:
--   The Hecke Split construction uses the inf Part inf Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/DegOneIffSurjective.lean#L68-L70

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

theorem GlobalTheory.HeckeSplit.infPart_infIdele (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.GlobalTheory.HeckeSplit.infIdele L x) = x := by sorry
