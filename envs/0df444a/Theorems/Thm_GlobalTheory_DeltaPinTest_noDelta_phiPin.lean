-- Prove2me | Theorems.Thm_GlobalTheory_DeltaPinTest_noDelta_phiPin
-- name    : GlobalTheory.DeltaPinTest.noDelta_phiPin
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:28.711853+00:00
-- url     : https://prove2.me/theorems/498ba315-41aa-4ab1-8b7a-bc30ba5f474e
-- title:
--   Delta Pin Test: no Delta phi Pin
-- statement:
--   The Delta Pin Test construction uses the no Delta phi Pin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/InducedEqOne.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/InducedEqOne.lean#L14-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_InducedEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DeltaPinTest
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem GlobalTheory.DeltaPinTest.noDelta_phiPin (nab : NabV Xo c) (m : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (noDelta Xo c nab m n).PhiPin (fun _ => 1) 1 (fun _ => 0) := by sorry
