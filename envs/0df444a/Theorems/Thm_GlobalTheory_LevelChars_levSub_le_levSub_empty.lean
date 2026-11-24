-- Prove2me | Theorems.Thm_GlobalTheory_LevelChars_levSub_le_levSub_empty
-- name    : GlobalTheory.LevelChars.levSub_le_levSub_empty
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:22.771724+00:00
-- url     : https://prove2.me/theorems/1c051ce3-c858-4a79-97f5-1e914e423f68
-- title:
--   Level Chars: lev Sub le lev Sub empty
-- statement:
--   The Level Chars construction uses the lev Sub le lev Sub empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassGroupIdelicFiniteIndex.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassGroupIdelicFiniteIndex.lean#L76-L77

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

theorem GlobalTheory.LevelChars.levSub_le_levSub_empty (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := by sorry
