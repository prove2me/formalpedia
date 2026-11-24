-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_card_eq
-- name    : GlobalTheory.ResultantNorm.card_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:18.692541+00:00
-- url     : https://prove2.me/theorems/3af337d8-f64c-40ae-84bc-31afcdc53932
-- title:
--   Resultant Norm: card eq
-- statement:
--   The Resultant Norm construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L151-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L151-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem GlobalTheory.ResultantNorm.card_eq (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] Ω] (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖) :
    a.card = b.card := by sorry
