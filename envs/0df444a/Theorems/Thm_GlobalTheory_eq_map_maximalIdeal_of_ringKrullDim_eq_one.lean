-- Prove2me | Theorems.Thm_GlobalTheory_eq_map_maximalIdeal_of_ringKrullDim_eq_one
-- name    : GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:17:31.229806+00:00
-- url     : https://prove2.me/theorems/a3904dd5-4b7c-45fa-b5c6-37253fd933fb
-- title:
--   Global Theory: eq map maximal Ideal of ring Krull Dim eq one
-- statement:
--   The Global Theory construction uses the eq map maximal Ideal of ring Krull Dim eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMapMaximalIdealOfRingKrullDimEqOne.lean#L6-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMapMaximalIdealOfRingKrullDimEqOne.lean#L6-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMapMaximalIdealOfRingKrullDimEqOne
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

theorem GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one (R A : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A]
    (p : Ideal A) [p.IsPrime] :
    (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 →
      IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) →
      p = (maximalIdeal R).map (algebraMap R A) := by sorry
