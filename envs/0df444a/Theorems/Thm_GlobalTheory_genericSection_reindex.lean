-- Prove2me | Theorems.Thm_GlobalTheory_genericSection_reindex
-- name    : GlobalTheory.genericSection_reindex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:27.9904+00:00
-- url     : https://prove2.me/theorems/00025173-dfe7-4237-bcf4-d7ec12ef1d96
-- title:
--   Global Theory: generic Section reindex
-- statement:
--   The Global Theory construction uses the generic Section reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GenericSectionInjectiveOfAxH.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GenericSectionInjectiveOfAxH.lean#L10-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GenericSectionInjectiveOfAxH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT

theorem GlobalTheory.genericSection_reindex {F : Type} [Field F] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → F) :
    ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x = sImg (D := D) j₀ x ∘
      (Equiv.prodCongr (Equiv.refl (Fin (D + 1))) (Fin.cycleRange j₀).symm) := by sorry
