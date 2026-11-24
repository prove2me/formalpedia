-- Prove2me | Theorems.Thm_GlobalTheory_InertNorm_finite_quotient_map_of_finite
-- name    : GlobalTheory.InertNorm.finite_quotient_map_of_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:57.83801+00:00
-- url     : https://prove2.me/theorems/1a66b828-cf89-4fdb-9b33-cfba2a72290e
-- title:
--   Inert Norm: finite quotient map of finite
-- statement:
--   The Inert Norm construction uses the finite quotient map of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L17-L23

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

theorem GlobalTheory.InertNorm.finite_quotient_map_of_finite {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by sorry
