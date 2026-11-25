-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_neOnComps_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.neOnComps_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:40.304306+00:00
-- url     : https://prove2.me/theorems/87b8f193-72a1-483b-8c46-e32c8d8898b7
-- title:
--   Zero Weight Sections: ne On Comps one
-- statement:
--   The Zero Weight Sections construction uses the ne On Comps one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L219-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L219-L222

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.neOnComps_one (h : GenFrEx Xo c) (ht : GenFromTest Xo c h) : NeOnComps h (1 : Rul Xo c) := by sorry
