-- Prove2me | Theorems.Thm_MassDataIdxEmb_quad_root
-- name    : MassDataIdxEmb.quad_root
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:50.392807+00:00
-- url     : https://prove2.me/theorems/807ec29f-87bd-4765-b270-018da6772ca5
-- title:
--   Mass Data Idx Emb: quad root
-- statement:
--   The Mass Data Idx Emb construction uses the quad root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/QuadRoot.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/QuadRoot.lean#L9-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxEmb
open Metric

theorem MassDataIdxEmb.quad_root {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c0 c1 : K) (h1 : ‖c1‖ = 1) (h0 : ‖c0‖ < 1) :
    ∃ x : K, x * x + c1 * x + c0 = 0 := by sorry
