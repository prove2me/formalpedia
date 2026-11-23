-- Prove2me | Theorems.Thm_GlobalTheory_exists_root_cubic
-- name    : GlobalTheory.exists_root_cubic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:25.664809+00:00
-- url     : https://prove2.me/theorems/08a4419d-255b-47d7-b0e6-ac367b4f1a33
-- title:
--   Global Theory: exists root cubic
-- statement:
--   The Global Theory construction uses the exists root cubic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean#L109-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {L : Type*} [Field L] [IsAlgClosed L]

theorem GlobalTheory.exists_root_cubic {a : L} (ha : a ≠ 0) (b c d : L) :
    ∃ x : L, a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by sorry
