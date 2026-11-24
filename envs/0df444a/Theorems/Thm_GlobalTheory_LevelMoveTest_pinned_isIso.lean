-- Prove2me | Theorems.Thm_GlobalTheory_LevelMoveTest_pinned_isIso
-- name    : GlobalTheory.LevelMoveTest.pinned_isIso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:02:52.198022+00:00
-- url     : https://prove2.me/theorems/f682ce57-adc4-4e4f-a50b-d913dc187f76
-- title:
--   Level Move Test: pinned is Iso
-- statement:
--   The Level Move Test construction uses the pinned is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/CarriedGeneratorUnique.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/CarriedGeneratorUnique.lean#L18-L32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_CarriedGeneratorUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelMoveTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem GlobalTheory.LevelMoveTest.pinned_isIso {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) :
    IsIso pm := by sorry
