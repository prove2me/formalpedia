-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_add_map_idem
-- name    : GlobalTheory.LevCover.add_map_idem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:16:17.231798+00:00
-- url     : https://prove2.me/theorems/6c40e90e-7b79-405b-958f-fffc154cb022
-- title:
--   Lev Cover: add map idem
-- statement:
--   The Lev Cover construction uses the add map idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsInducedLocus.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsInducedLocus.lean#L131-L135

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsInducedLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
variable {l : Level H}

theorem GlobalTheory.LevCover.add_map_idem {Q : Type} [Group Q] {l₂ : Level H} {e : 𝓞 E} (he' : 1 - e ∈ l₂.Mb) {f : D.La → Q}
    (hf : ∀ a c, f (a + c) = f a * f c) (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), f a = 1) (a : D.La) :
    f (e • a) = f a := by sorry
