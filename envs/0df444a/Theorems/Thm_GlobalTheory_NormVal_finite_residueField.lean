-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_finite_residueField
-- name    : GlobalTheory.NormVal.finite_residueField
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:35.333918+00:00
-- url     : https://prove2.me/theorems/254f0b6c-fe32-52f1-9171-85fd26126c0b
-- title:
--   Norm Val: finite residue Field
-- statement:
--   The Norm Val construction uses the finite residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L133-L139

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

theorem GlobalTheory.NormVal.finite_residueField (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B]
    [IsLocalRing B] [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B]
    [IsScalarTower R S B] [IsLocalHom (algebraMap R B)] :
    Module.Finite (ResidueField R) (ResidueField B) := by sorry
