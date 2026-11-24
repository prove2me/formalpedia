-- Prove2me | Theorems.Thm_GlobalTheory_LengthQuotientValuationDet_length_quotient_eq_addVal_det
-- name    : GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:28.818945+00:00
-- url     : https://prove2.me/theorems/1a391378-ef68-49a7-ada6-b3cfc0da7bff
-- title:
--   Length Quotient Valuation Det: length quotient eq add Val det
-- statement:
--   The Length Quotient Valuation Det construction uses the length quotient eq add Val det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L25-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean#L25-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthQuotientValuationDet
open Module IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by sorry
