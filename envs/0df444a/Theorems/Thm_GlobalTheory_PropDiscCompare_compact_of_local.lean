-- Prove2me | Theorems.Thm_GlobalTheory_PropDiscCompare_compact_of_local
-- name    : GlobalTheory.PropDiscCompare.compact_of_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:46.425718+00:00
-- url     : https://prove2.me/theorems/059206af-9aa2-4978-b772-a2b8b65607d8
-- title:
--   Prop Disc Compare: compact of local
-- statement:
--   The Prop Disc Compare construction uses the compact of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteOfLocallyFinite.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteOfLocallyFinite.lean#L15-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ProperlyDiscontinuousFlags
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteOfLocallyFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PropDiscCompare
open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.PropDiscCompare.compact_of_local (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags.ProperlyDiscontinuousOnFlags X := by sorry
