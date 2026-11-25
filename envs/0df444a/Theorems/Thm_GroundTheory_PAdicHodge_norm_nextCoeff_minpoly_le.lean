-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_nextCoeff_minpoly_le
-- name    : GroundTheory.PAdicHodge.norm_nextCoeff_minpoly_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:56.146683+00:00
-- url     : https://prove2.me/theorems/9c1737bc-e382-4960-a309-d0d3cda7d250
-- title:
--   PAdic Hodge: norm next Coeff minpoly le
-- statement:
--   The PAdic Hodge construction uses the norm next Coeff minpoly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L306-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTrace.lean#L306-L320

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.norm_nextCoeff_minpoly_le (F : Type*) [Field F] [Algebra ℚ_[p] F] [Algebra F (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] F (PadicAlgCl p)] (y : PadicAlgCl p) :
    ‖algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff‖ ≤ ‖y‖ := by sorry
