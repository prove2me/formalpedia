-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_Charts_ofTorus_pull_split
-- name    : GlobalTheory.ZJ.Charts.ofTorus_pull_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:16.159018+00:00
-- url     : https://prove2.me/theorems/5d361d30-ae44-4cd5-99e7-5ed936fafe33
-- title:
--   Charts: of Torus pull split
-- statement:
--   The Charts construction uses the of Torus pull split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsAffineSplitTorusLeft.lean#L250-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsAffineSplitTorusLeft.lean#L250-L300

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

theorem GlobalTheory.ZJ.Charts.ofTorus_pull_split (S : Scheme.{0}) [IsAffine S] (d : ℕ) {S' : Scheme.{0}} (t : S' ⟶ S)
    [IsAffineHom (pullback.fst (splitTorus S (Fin d → ℤ)).hom t)] :
    Charts.Split (H := (Over.pullback t).obj (splitTorus S (Fin d → ℤ))) (d := d)
      ((Charts.ofTorus S d).pull (pullback.fst (splitTorus S (Fin d → ℤ)).hom t)) some := by sorry
