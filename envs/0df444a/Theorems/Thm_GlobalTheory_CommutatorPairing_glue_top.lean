-- Prove2me | Theorems.Thm_GlobalTheory_CommutatorPairing_glue_top
-- name    : GlobalTheory.CommutatorPairing.glue_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:16:58.728836+00:00
-- url     : https://prove2.me/theorems/eca08217-a66f-45ba-9293-6da4385a0310
-- title:
--   Commutator Pairing: glue top
-- statement:
--   The Commutator Pairing construction uses the glue top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueWeilIs.lean#L42-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing

theorem GlobalTheory.CommutatorPairing.glue_top {Y : Scheme.{0}} {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (c : ∀ s, Γ((W s).toScheme, ⊤)ˣ)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z),
      r ≫ (W s).ι = r' ≫ (W s').ι → gm r z ⊤ (c s) = gm r' z ⊤ (c s')) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z),
      gm (r ≫ (W s).ι) z ⊤ a = gm r z ⊤ (c s) := by sorry
