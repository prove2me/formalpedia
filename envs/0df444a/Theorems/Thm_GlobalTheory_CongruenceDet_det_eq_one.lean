-- Prove2me | Theorems.Thm_GlobalTheory_CongruenceDet_det_eq_one
-- name    : GlobalTheory.CongruenceDet.det_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:29.896829+00:00
-- url     : https://prove2.me/theorems/74939c07-1ec7-4e16-829a-65cfb6e137b5
-- title:
--   Congruence Det: det eq one
-- statement:
--   The Congruence Det construction uses the det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L154-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralDetSubOne.lean#L154-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors

theorem GlobalTheory.CongruenceDet.det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), Gm.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by sorry
