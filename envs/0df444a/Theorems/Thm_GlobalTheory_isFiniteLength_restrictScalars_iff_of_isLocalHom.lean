-- Prove2me | Theorems.Thm_GlobalTheory_isFiniteLength_restrictScalars_iff_of_isLocalHom
-- name    : GlobalTheory.isFiniteLength_restrictScalars_iff_of_isLocalHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:25.206915+00:00
-- url     : https://prove2.me/theorems/5789386d-f5b9-4552-9fc7-9fee16ba9536
-- title:
--   Global Theory: is Finite Length restrict Scalars iff of is Local Hom
-- statement:
--   The Global Theory construction uses the is Finite Length restrict Scalars iff of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L18-L29

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
variable (R S X : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]

theorem GlobalTheory.isFiniteLength_restrictScalars_iff_of_isLocalHom
    [Module.Finite (ResidueField R) (ResidueField S)] :
    IsFiniteLength R X ↔ IsFiniteLength S X := by sorry
