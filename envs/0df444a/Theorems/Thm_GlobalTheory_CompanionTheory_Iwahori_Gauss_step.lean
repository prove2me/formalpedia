-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_step
-- name    : GlobalTheory.CompanionTheory.Iwahori.Gauss.step
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:49:45.261807+00:00
-- url     : https://prove2.me/theorems/906ebb45-c95b-4038-a9dd-b689e4dcd027
-- title:
--   Gauss: step
-- statement:
--   The Gauss construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L76-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriUpperLowerFactorization.lean#L76-L195

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}

theorem GlobalTheory.CompanionTheory.Iwahori.Gauss.step (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ)
    (ih : ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b)
    (q : ι) (hq : wt q = m) (x : E) (hx : x ∈ J)
    (hH : ∀ i j, (m + 1 ≤ wt i ∨ m + 1 ≤ wt j) → P i * x * P j = 0) :
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ 1 + x = a * b := by sorry
