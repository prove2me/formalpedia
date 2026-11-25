-- Prove2me | Theorems.Thm_GlobalTheory_T_card_inertia_eq_ramificationIdx_of_perfect_residue
-- name    : GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:23.46851+00:00
-- url     : https://prove2.me/theorems/6966e560-7d88-5acf-84dc-8889cac75e28
-- title:
--   T: card inertia eq ramification Idx of perfect residue
-- statement:
--   The T construction uses the card inertia eq ramification Idx of perfect residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidueStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardInertiaEqRamificationIdxOfPerfectResidueStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)), Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by sorry
