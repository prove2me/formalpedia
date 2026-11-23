-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_isUnit_of_isIntegralElem
-- name    : GlobalTheory.ArcConst.isUnit_of_isIntegralElem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:29.812351+00:00
-- url     : https://prove2.me/theorems/47f19497-6164-4257-896e-e5008ff28a5d
-- title:
--   Arc Const: is Unit of is Integral Elem
-- statement:
--   The Arc Const construction uses the is Unit of is Integral Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L28-L31

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

theorem GlobalTheory.ArcConst.isUnit_of_isIntegralElem {K A : Type} [Field K] [CommRing A] [IsDomain A] (f : K →+* A)
    {s : A} (hs : f.IsIntegralElem s) (h0 : s ≠ 0) : IsUnit s := by sorry
