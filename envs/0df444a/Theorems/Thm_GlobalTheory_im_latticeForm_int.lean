-- Prove2me | Theorems.Thm_GlobalTheory_im_latticeForm_int
-- name    : GlobalTheory.im_latticeForm_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:12.839271+00:00
-- url     : https://prove2.me/theorems/2229e2a0-4e7f-4805-b899-467c571585c3
-- title:
--   Global Theory: im lattice Form int
-- statement:
--   The Global Theory construction uses the im lattice Form int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L958-L963
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/HasSumLocallyUniformlyWeierstrassZetaExcept.lean#L958-L963

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.im_latticeForm_int (m n m' n' : ℤ) :
    (latticeForm L (m * L.ω₁ + n * L.ω₂) (m' * L.ω₁ + n' * L.ω₂)).im =
      (n * m' - m * n' : ℤ) * (latticeForm L L.ω₂ L.ω₁).im := by sorry
