-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_arcDet_ne_zero
-- name    : GlobalTheory.ArcConst.arcDet_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:00.086498+00:00
-- url     : https://prove2.me/theorems/be22a691-7d0f-4093-93cd-979514433d75
-- title:
--   Arc Const: arc Det ne zero
-- statement:
--   The Arc Const construction uses the arc Det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L79-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.ArcConst.arcDet_ne_zero (Dw : Datum H) (K : Type) [Field K] : arcDet Dw K ≠ 0 := by sorry
