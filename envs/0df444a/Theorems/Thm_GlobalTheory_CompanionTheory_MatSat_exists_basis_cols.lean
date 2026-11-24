-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatSat_exists_basis_cols
-- name    : GlobalTheory.CompanionTheory.MatSat.exists_basis_cols
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:53:05.809122+00:00
-- url     : https://prove2.me/theorems/03b7fd83-8954-4209-91e7-c41179fe0f80
-- title:
--   Mat Sat: exists basis cols
-- statement:
--   The Mat Sat construction uses the exists basis cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsBasisCols.lean#L8-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/ExistsBasisCols.lean#L8-L75

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

theorem GlobalTheory.CompanionTheory.MatSat.exists_basis_cols {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by sorry
