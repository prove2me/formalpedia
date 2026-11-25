-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_neOnComps_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.neOnComps_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:20.659864+00:00
-- url     : https://prove2.me/theorems/8189e77a-f328-451d-ab3f-44767cd4446f
-- title:
--   Zero Weight Sections: ne On Comps iff
-- statement:
--   The Zero Weight Sections construction uses the ne On Comps iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L215-L217

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.neOnComps_iff (h : GenFrEx Xo c) (G : WTZ E) (f : Rul Xo c) :
    NeOnComps h f ↔ ∀ Z, valZ h G f Z ≠ 0 := by sorry
