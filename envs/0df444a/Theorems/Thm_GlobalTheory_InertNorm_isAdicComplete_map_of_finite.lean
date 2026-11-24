-- Prove2me | Theorems.Thm_GlobalTheory_InertNorm_isAdicComplete_map_of_finite
-- name    : GlobalTheory.InertNorm.isAdicComplete_map_of_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:16:24.001781+00:00
-- url     : https://prove2.me/theorems/02adb6f9-e859-4d13-8e1c-c2c5b1947f9a
-- title:
--   Inert Norm: is Adic Complete map of finite
-- statement:
--   The Inert Norm construction uses the is Adic Complete map of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselianStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.InertNorm

theorem GlobalTheory.InertNorm.isAdicComplete_map_of_finite {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by sorry
