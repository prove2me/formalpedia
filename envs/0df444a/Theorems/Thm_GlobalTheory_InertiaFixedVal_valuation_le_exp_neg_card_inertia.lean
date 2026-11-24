-- Prove2me | Theorems.Thm_GlobalTheory_InertiaFixedVal_valuation_le_exp_neg_card_inertia
-- name    : GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:42.349795+00:00
-- url     : https://prove2.me/theorems/d293d004-a18d-4d59-bbc1-022c4d9cdb3d
-- title:
--   Inertia Fixed Val: valuation le exp neg card inertia
-- statement:
--   The Inertia Fixed Val construction uses the valuation le exp neg card inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationLeExpNegCardInertiaOfInertiaFixed.lean#L6-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuationLeExpNegCardInertiaOfInertiaFixed.lean#L6-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationLeExpNegCardInertiaOfInertiaFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory GlobalTheory.InertiaFixedVal

theorem GlobalTheory.InertiaFixedVal.valuation_le_exp_neg_card_inertia (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)) (y : L) :
    (∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) → P.valuation L y < 1 →
      P.valuation L y ≤ WithZero.exp (-(Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) : ℤ)) := by sorry
