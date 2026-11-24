-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_algebraMap_injective
-- name    : GlobalTheory.ArcConst.algebraMap_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:58:53.001393+00:00
-- url     : https://prove2.me/theorems/3c848258-5541-4ba1-9686-7899c2ff5611
-- title:
--   Arc Const: algebra Map injective
-- statement:
--   The Arc Const construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L91-L94

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

theorem GlobalTheory.ArcConst.algebraMap_injective (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) := by sorry
