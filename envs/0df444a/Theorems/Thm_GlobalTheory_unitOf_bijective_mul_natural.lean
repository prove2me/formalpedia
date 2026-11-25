-- Prove2me | Theorems.Thm_GlobalTheory_unitOf_bijective_mul_natural
-- name    : GlobalTheory.unitOf_bijective_mul_natural
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:59.896008+00:00
-- url     : https://prove2.me/theorems/8566ab45-5670-5a57-a399-d0294811d416
-- title:
--   Global Theory: unit Of bijective mul natural
-- statement:
--   The Global Theory construction uses the unit Of bijective mul natural property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitOfBijectiveMulNatural.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitOfBijectiveMulNatural.lean#L83-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.unitOf_bijective_mul_natural :
    ∀ (O : Type) [CommRing O], (∀ (R : Type) [CommRing R] [Algebra O R], Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) ∧ ∀ w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O)), unitOf (w * w') = unitOf w * unitOf w') ∧ ∀ (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))), (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by sorry
