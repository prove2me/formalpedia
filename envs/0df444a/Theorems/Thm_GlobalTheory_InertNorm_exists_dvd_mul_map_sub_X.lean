-- Prove2me | Theorems.Thm_GlobalTheory_InertNorm_exists_dvd_mul_map_sub_X
-- name    : GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:15:48.260795+00:00
-- url     : https://prove2.me/theorems/24f48c32-bbe8-4be8-afae-dce317b8e649
-- title:
--   Inert Norm: exists dvd mul map sub X
-- statement:
--   The Inert Norm construction uses the exists dvd mul map sub X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L25-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsNormEqXModMonicOfAdicCompleteInvolution.lean#L25-L73

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

theorem GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by sorry
