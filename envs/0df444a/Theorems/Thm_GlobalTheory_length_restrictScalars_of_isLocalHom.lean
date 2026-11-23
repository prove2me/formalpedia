-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_of_isLocalHom
-- name    : GlobalTheory.length_restrictScalars_of_isLocalHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:30.850038+00:00
-- url     : https://prove2.me/theorems/1356c263-643e-4491-8b38-4b166ac9acb7
-- title:
--   Global Theory: length restrict Scalars of is Local Hom
-- statement:
--   The Global Theory construction uses the length restrict Scalars of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L12-L16

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

theorem GlobalTheory.length_restrictScalars_of_isLocalHom
    [Module.Finite (ResidueField R) (ResidueField S)] :
    Module.length R X =
      Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) := by sorry
