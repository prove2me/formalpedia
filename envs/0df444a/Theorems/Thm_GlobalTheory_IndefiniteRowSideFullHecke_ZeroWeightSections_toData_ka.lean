-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_toData_ka
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.toData_ka
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:23.858803+00:00
-- url     : https://prove2.me/theorems/3b61d338-cd7c-4a26-89ce-268fc67ab256
-- title:
--   Zero Weight Sections: to Data ka
-- statement:
--   The Zero Weight Sections construction uses the to Data ka property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L230-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SectionInputData.lean#L230-L230

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
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.toData_ka : (I.toData h δ fn yP).ka = I.wka := by sorry
