-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_inertiaDeg_eq_finrank_residueField
-- name    : GlobalTheory.NormVal.inertiaDeg_eq_finrank_residueField
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:57.822666+00:00
-- url     : https://prove2.me/theorems/d50c73a5-5439-4d8e-b3cb-a3693e091238
-- title:
--   Norm Val: inertia Deg eq finrank residue Field
-- statement:
--   The Norm Val construction uses the inertia Deg eq finrank residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L119-L131

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

theorem GlobalTheory.NormVal.inertiaDeg_eq_finrank_residueField (n : Ideal S) [n.IsMaximal] (B : Type*) [CommRing B]
    [IsLocalRing B] [Algebra S B] [IsLocalization.AtPrime B n] [Algebra R B]
    [IsScalarTower R S B] [IsLocalHom (algebraMap R B)] :
    n.inertiaDeg R = Module.finrank (ResidueField R) (ResidueField B) := by sorry
