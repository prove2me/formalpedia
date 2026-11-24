-- Prove2me | Theorems.Thm_GlobalTheory_HolPeriods_isHolTo_of_local
-- name    : GlobalTheory.HolPeriods.isHolTo_of_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:35.708235+00:00
-- url     : https://prove2.me/theorems/09c2cf79-7df3-4655-94fc-59358b6efabb
-- title:
--   Hol Periods: is Hol To of local
-- statement:
--   The Hol Periods construction uses the is Hol To of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L37-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L37-L47

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
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}

theorem GlobalTheory.HolPeriods.isHolTo_of_local {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : ∀ b ∈ B, ∃ B' : Set V, b ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y) : IsHolTo B y := by sorry
