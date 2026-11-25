-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_local_and_semilocal
-- name    : GlobalTheory.length_restrictScalars_local_and_semilocal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:58.948354+00:00
-- url     : https://prove2.me/theorems/e5912534-ab05-46fd-89ce-9ea14bb46c02
-- title:
--   Global Theory: length restrict Scalars local and semilocal
-- statement:
--   The Global Theory construction uses the length restrict Scalars local and semilocal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L295-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L295-L306

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

theorem GlobalTheory.length_restrictScalars_local_and_semilocal (R S X : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [AddCommGroup X] [Module R X] [Module S X]
    [IsScalarTower R S X] (h : IsFiniteLength S X) :
    (∀ [IsLocalRing S] [IsLocalHom (algebraMap R S)]
      [Module.Finite (ResidueField R) (ResidueField S)],
      Module.length R X =
        Module.length S X * (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞)) ∧
    (∀ [Module.Finite R S], Finite (MaximalSpectrum S) ∧ ∀ [Fintype (MaximalSpectrum S)],
      Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
        (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞)) := by sorry
