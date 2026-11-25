-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_padicInt_OL_injective
-- name    : GlobalTheory.algebraMap_padicInt_OL_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:12.45879+00:00
-- url     : https://prove2.me/theorems/f5570a8a-d9f7-4693-9aeb-a2fe7f9ccb14
-- title:
--   Global Theory: algebra Map padic Int OL injective
-- statement:
--   The Global Theory construction uses the algebra Map padic Int OL injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapPadicIntFinExtInjective.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AlgebraMapPadicIntFinExtInjective.lean#L20-L23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory

theorem GlobalTheory.algebraMap_padicInt_OL_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by sorry
