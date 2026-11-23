-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_of_extend_adicCompletion
-- name    : GlobalTheory.isLocalHom_of_extend_adicCompletion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:00.274952+00:00
-- url     : https://prove2.me/theorems/f9e2e467-e9b0-42c5-83a7-1f63b2483a2c
-- title:
--   Global Theory: is Local Hom of extend adic Completion
-- statement:
--   The Global Theory construction uses the is Local Hom of extend adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L95-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]

theorem GlobalTheory.isLocalHom_of_extend_adicCompletion [IsLocalRing A] [IsLocalRing R]
    (hJ : (maximalIdeal A).FG) (ψ : AdicCompletion (maximalIdeal A) A →+* R)
    [hψ : IsLocalHom (ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))] :
    IsLocalHom ψ := by sorry
