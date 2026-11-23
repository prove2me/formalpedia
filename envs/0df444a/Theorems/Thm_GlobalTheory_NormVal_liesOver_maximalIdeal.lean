-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_liesOver_maximalIdeal
-- name    : GlobalTheory.NormVal.liesOver_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:32.342199+00:00
-- url     : https://prove2.me/theorems/7a141781-2172-4ee6-9966-f7c335ae23f5
-- title:
--   Norm Val: lies Over maximal Ideal
-- statement:
--   The Norm Val construction uses the lies Over maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L98-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]

theorem GlobalTheory.NormVal.liesOver_maximalIdeal (n : Ideal S) [n.IsMaximal] : n.LiesOver (maximalIdeal R) := by sorry
