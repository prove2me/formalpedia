-- Prove2me | Theorems.Thm_GlobalTheory_InertiaDVR_card_inertia_eq_ramificationIdx
-- name    : GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:35.665858+00:00
-- url     : https://prove2.me/theorems/3ec06952-28bc-4d08-97c3-17a781bcad4d
-- title:
--   Inertia DVR: card inertia eq ramification Idx
-- statement:
--   The Inertia DVR construction uses the card inertia eq ramification Idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidue.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidue.lean#L20-L43

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

theorem GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L]
    [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)),
    Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by sorry
