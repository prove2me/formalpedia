-- Prove2me | Theorems.Thm_GlobalTheory_powerSeriesPrimeX_asIdeal
-- name    : GlobalTheory.powerSeriesPrimeX_asIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:57.875465+00:00
-- url     : https://prove2.me/theorems/b38447e7-09dd-4267-9510-a285be86f316
-- title:
--   Global Theory: power Series Prime X as Ideal
-- statement:
--   The Global Theory construction uses the power Series Prime X as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/StalkGenericPointSpecializesOfSpecializes.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/StalkGenericPointSpecializesOfSpecializes.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
open GlobalTheory
open PowerSeries

theorem GlobalTheory.powerSeriesPrimeX_asIdeal (O : Type u) [CommRing O] [IsDomain O] :
    (powerSeriesPrimeX O).asIdeal = Ideal.span {(X : O⟦X⟧)} := by sorry

attribute [defeq] GlobalTheory.powerSeriesPrimeX_asIdeal
