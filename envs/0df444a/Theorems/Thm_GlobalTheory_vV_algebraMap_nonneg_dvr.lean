-- Prove2me | Theorems.Thm_GlobalTheory_vV_algebraMap_nonneg_dvr
-- name    : GlobalTheory.vV_algebraMap_nonneg_dvr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:55.66979+00:00
-- url     : https://prove2.me/theorems/3e8be1ca-c484-403d-8fd3-6ebe9e3bb4ca
-- title:
--   Global Theory: v V algebra Map nonneg dvr
-- statement:
--   The Global Theory construction uses the v V algebra Map nonneg dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/VVAlgebraMapNonnegDvr.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/VVAlgebraMapNonnegDvr.lean#L8-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory

theorem GlobalTheory.vV_algebraMap_nonneg_dvr (T : CDVR) (x : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr x) := by sorry
