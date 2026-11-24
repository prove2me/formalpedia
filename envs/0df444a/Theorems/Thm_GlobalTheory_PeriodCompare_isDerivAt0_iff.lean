-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCompare_isDerivAt0_iff
-- name    : GlobalTheory.PeriodCompare.isDerivAt0_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:11.469926+00:00
-- url     : https://prove2.me/theorems/883aab1d-102f-42ca-9c5b-2a5f123e8517
-- title:
--   Period Compare: is Deriv At0 iff
-- statement:
--   The Period Compare construction uses the is Deriv At0 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L259-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L259-L278

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

theorem GlobalTheory.PeriodCompare.isDerivAt0_iff {g : ℕ} {F : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {B : Set (Fin g → ℂ)} (hB : B ∈ 𝓝 0) (hF : HolOn B F)
    (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 F w v ↔ IsDerivAlong F w v := by sorry
