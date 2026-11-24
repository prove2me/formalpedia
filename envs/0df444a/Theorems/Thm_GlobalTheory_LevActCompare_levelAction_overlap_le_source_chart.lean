-- Prove2me | Theorems.Thm_GlobalTheory_LevActCompare_levelAction_overlap_le_source_chart
-- name    : GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:01:40.559374+00:00
-- url     : https://prove2.me/theorems/1bc919cd-a31e-4e37-8e61-2f979a6e2077
-- title:
--   Lev Act Compare: level Action overlap le source chart
-- statement:
--   The Lev Act Compare construction uses the level Action overlap le source chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LevelActionOverlapLeSourceChart.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/LevelActionOverlapLeSourceChart.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelPairAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevActCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (x : Sp S ⟶ Xo.X)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      (PPx x).U (fun _ => j) := by sorry
