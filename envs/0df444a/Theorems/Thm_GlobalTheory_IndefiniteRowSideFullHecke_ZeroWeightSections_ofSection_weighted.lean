-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_ofSection_weighted
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.ofSection_weighted
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:48.001672+00:00
-- url     : https://prove2.me/theorems/11c434f8-985b-4d5f-a2e6-73348adc83bd
-- title:
--   Zero Weight Sections: of Section weighted
-- statement:
--   The Zero Weight Sections construction uses the of Section weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L294-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L294-L305

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable (Xo c)
variable {Xo c}

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.ofSection_weighted (D T : ℕ) {L : WTZ E} {s : Rul Xo c} (hs : IsSecZ L s) :
    (ofSection D T L s).Weighted := by sorry
