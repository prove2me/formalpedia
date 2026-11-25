-- Prove2me | Theorems.Thm_GlobalTheory_FinExtIntegers_dvr_complete
-- name    : GlobalTheory.FinExtIntegers.dvr_complete
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:53:41.160944+00:00
-- url     : https://prove2.me/theorems/b75f8e9c-ba0e-5ed9-abd4-0011dd765196
-- title:
--   Fin Ext Integers: dvr complete
-- statement:
--   The Fin Ext Integers construction uses the dvr complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrComplete.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrComplete.lean#L10-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.FinExtIntegers

theorem GlobalTheory.FinExtIntegers.dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by sorry
