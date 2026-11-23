-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_AlgZ_map
-- name    : GlobalTheory.ArcConst.AlgZ.map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:59.458036+00:00
-- url     : https://prove2.me/theorems/06be6db0-f21d-4a82-aae0-d3d81463dbdc
-- title:
--   Alg Z: map
-- statement:
--   The Alg Z construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L16-L17

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

theorem GlobalTheory.ArcConst.AlgZ.map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {s : A} (h : AlgZ s) : AlgZ (f s) := by sorry
