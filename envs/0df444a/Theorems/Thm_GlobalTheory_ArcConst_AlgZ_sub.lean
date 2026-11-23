-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_AlgZ_sub
-- name    : GlobalTheory.ArcConst.AlgZ.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:14.667422+00:00
-- url     : https://prove2.me/theorems/31dabc69-982e-4039-aaec-ec70977289fc
-- title:
--   Alg Z: sub
-- statement:
--   The Alg Z construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L19-L20

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

theorem GlobalTheory.ArcConst.AlgZ.sub {A : Type} [CommRing A] {s t : A} (h : AlgZ s) (h' : AlgZ t) : AlgZ (s - t) := by sorry
