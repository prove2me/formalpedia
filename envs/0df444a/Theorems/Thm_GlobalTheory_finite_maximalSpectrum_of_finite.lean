-- Prove2me | Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite
-- name    : GlobalTheory.finite_maximalSpectrum_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:46.325664+00:00
-- url     : https://prove2.me/theorems/259f169f-96ac-452e-be65-3b034dab7c64
-- title:
--   Global Theory: finite maximal Spectrum of finite
-- statement:
--   The Global Theory construction uses the finite maximal Spectrum of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L247-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L247-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

theorem GlobalTheory.finite_maximalSpectrum_of_finite [Module.Finite R S] : Finite (MaximalSpectrum S) := by sorry
