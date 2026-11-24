-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_PowVanish_exists_iso_tw
-- name    : GlobalTheory.AbLaw.PowVanish.exists_iso_tw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:21.979805+00:00
-- url     : https://prove2.me/theorems/5ae10e8d-8fc1-4fb1-999d-1371bb1fcf26
-- title:
--   Pow Vanish: exists iso tw
-- statement:
--   The Pow Vanish construction uses the exists iso tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesDescent.lean#L123-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesDescent.lean#L123-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish

theorem GlobalTheory.AbLaw.PowVanish.exists_iso_tw {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : X ⟶ X) (k n r N t : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![k, -1])) (hα : α.IsGen) (h : k * n = r + N * t) :
    ∃ w : LB.Iso ((pw L n).pull f) ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)), w.IsGen := by sorry
