-- Prove2me | Theorems.Thm_GlobalTheory_T_valuation_le_exp_neg_card_inertia_of_inertia_fixed
-- name    : GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:40:34.590897+00:00
-- url     : https://prove2.me/theorems/2de9c523-9280-46dd-9ec1-eeff99d5dfb2
-- title:
--   T: valuation le exp neg card inertia of inertia fixed
-- statement:
--   The T construction uses the valuation le exp neg card inertia of inertia fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationLeExpNegCardInertiaOfInertiaFixedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationLeExpNegCardInertiaOfInertiaFixedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixed
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixedStatement
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

theorem GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L), (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 → P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by sorry
