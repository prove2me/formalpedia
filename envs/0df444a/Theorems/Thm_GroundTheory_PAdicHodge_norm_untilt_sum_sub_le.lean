-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_untilt_sum_sub_le
-- name    : GroundTheory.PAdicHodge.norm_untilt_sum_sub_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:02.071343+00:00
-- url     : https://prove2.me/theorems/df9dbc84-2674-41b9-9e3b-54358ba04a19
-- title:
--   PAdic Hodge: norm untilt sum sub le
-- statement:
--   The PAdic Hodge construction uses the norm untilt sum sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L87-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L87-L103

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.norm_untilt_sum_sub_le {ι : Type*} (s : Finset ι) (x : ι → PreTilt (normInteger K) p) :
    ‖(((∑ i ∈ s, x i).untilt : normInteger K) : K) - ∑ i ∈ s, ((x i).untilt : K)‖ ≤
      ‖(p : K)‖ := by sorry
