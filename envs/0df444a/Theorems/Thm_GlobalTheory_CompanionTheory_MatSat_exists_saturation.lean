-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatSat_exists_saturation
-- name    : GlobalTheory.CompanionTheory.MatSat.exists_saturation
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:41.472203+00:00
-- url     : https://prove2.me/theorems/e0166a39-ed49-4a13-b00e-bba40562e7be
-- title:
--   Mat Sat: exists saturation
-- statement:
--   The Mat Sat construction uses the exists saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsBasisCols.lean#L77-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsBasisCols.lean#L77-L139

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsBasisCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatSat

theorem GlobalTheory.CompanionTheory.MatSat.exists_saturation {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by sorry
