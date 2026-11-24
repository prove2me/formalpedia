-- Prove2me | Theorems.Thm_GlobalTheory_HolPeriods_isDerivAt0_comp_equiv
-- name    : GlobalTheory.HolPeriods.isDerivAt0_comp_equiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:15.550808+00:00
-- url     : https://prove2.me/theorems/f3d65849-7bc8-4929-8976-6be020b0e40d
-- title:
--   Hol Periods: is Deriv At0 comp equiv
-- statement:
--   The Hol Periods construction uses the is Deriv At0 comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L119-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods

theorem GlobalTheory.HolPeriods.isDerivAt0_comp_equiv {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (k z)) w v ↔ IsDerivAt0 e (k w) v := by sorry
