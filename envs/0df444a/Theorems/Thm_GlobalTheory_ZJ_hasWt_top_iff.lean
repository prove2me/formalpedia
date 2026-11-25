-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_hasWt_top_iff
-- name    : GlobalTheory.ZJ.hasWt_top_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:36.454636+00:00
-- url     : https://prove2.me/theorems/4b1b5acb-99db-4c4f-8fc9-9c5bc1a1aceb
-- title:
--   ZJ: has Wt top iff
-- statement:
--   The ZJ construction uses the has Wt top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsAffineSplitTorusLeft.lean#L226-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsAffineSplitTorusLeft.lean#L226-L235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]

theorem GlobalTheory.ZJ.hasWt_top_iff (i : splitTorus S X ⟶ H) (u : Γ(H.left, ⊤)) (χ : X) :
    HasWt i ⊤ u χ ↔ ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H),
      ((t ≫ i) * g).left.appTop.hom u = t.left.appTop.hom (charUnit S X χ).val * g.left.appTop.hom u := by sorry
