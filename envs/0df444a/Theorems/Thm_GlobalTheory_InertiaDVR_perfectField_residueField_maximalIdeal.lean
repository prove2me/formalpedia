-- Prove2me | Theorems.Thm_GlobalTheory_InertiaDVR_perfectField_residueField_maximalIdeal
-- name    : GlobalTheory.InertiaDVR.perfectField_residueField_maximalIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:27.745882+00:00
-- url     : https://prove2.me/theorems/9c436124-8161-499e-ac11-3038397c498c
-- title:
--   Inertia DVR: perfect Field residue Field maximal Ideal
-- statement:
--   The Inertia DVR construction uses the perfect Field residue Field maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidue.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidue.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory GlobalTheory.InertiaDVR

theorem GlobalTheory.InertiaDVR.perfectField_residueField_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)] (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    PerfectField p.ResidueField := by sorry
