-- Prove2me | Theorems.Thm_GlobalTheory_LevelChars_finiteIndex_range_sup_levSub_empty
-- name    : GlobalTheory.LevelChars.finiteIndex_range_sup_levSub_empty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:29.694346+00:00
-- url     : https://prove2.me/theorems/685ee871-dd69-460f-950f-7c836d7f4b3b
-- title:
--   Level Chars: finite Index range sup lev Sub empty
-- statement:
--   The Level Chars construction uses the finite Index range sup lev Sub empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassGroupIdelicFiniteIndex.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassGroupIdelicFiniteIndex.lean#L79-L88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassGroupIdelicFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars

theorem GlobalTheory.LevelChars.finiteIndex_range_sup_levSub_empty (L : Type) [Field L] [NumberField L] :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L ∅ 0).FiniteIndex := by sorry
