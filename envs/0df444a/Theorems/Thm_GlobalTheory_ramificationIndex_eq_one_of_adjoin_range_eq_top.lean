-- Prove2me | Theorems.Thm_GlobalTheory_ramificationIndex_eq_one_of_adjoin_range_eq_top
-- name    : GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:20.062464+00:00
-- url     : https://prove2.me/theorems/0e557372-cb42-4238-be82-f8dfcceb82d1
-- title:
--   Global Theory: ramification Index eq one of adjoin range eq top
-- statement:
--   The Global Theory construction uses the ramification Index eq one of adjoin range eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RamificationIndexEqOneOfAdjoinRangeEqTop.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RamificationIndexEqOneOfAdjoinRangeEqTop.lean#L10-L44

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RamificationIndexEqOneOfAdjoinRangeEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory
open GroundTheory.LocalField IntermediateField

theorem GlobalTheory.ramificationIndex_eq_one_of_adjoin_range_eq_top (F E K L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L]
    [ValuativeExtension F E] [ValuativeExtension F K] [ValuativeExtension K L]
    [FiniteDimensional F E] [FiniteDimensional K L] :
    GroundTheory.LocalField.ramificationIndex F E = 1 →
      Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
        GroundTheory.LocalField.ramificationIndex K L = 1 := by sorry
