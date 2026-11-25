-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCompare_val_spMap
-- name    : GlobalTheory.PeriodCompare.val_spMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:19.803081+00:00
-- url     : https://prove2.me/theorems/ba2febfa-c607-4c4c-a560-2a4c6579990a
-- title:
--   Period Compare: val sp Map
-- statement:
--   The Period Compare construction uses the val sp Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L280-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L280-L285

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

theorem GlobalTheory.PeriodCompare.val_spMap {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (f : Γ(Sp A, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((spMap φ).appLE ⊤ ⊤ h).hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom f) := by sorry
