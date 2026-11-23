-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono
-- name    : GroundTheory.PAdicHodge.cyclotomicLayer_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:42.258919+00:00
-- url     : https://prove2.me/theorems/f5171d15-4a00-4bbc-9478-c3e1bc9e0239
-- title:
--   PAdic Hodge: cyclotomic Layer mono
-- statement:
--   The PAdic Hodge construction uses the cyclotomic Layer mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
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
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem GroundTheory.PAdicHodge.cyclotomicLayer_mono : Monotone (cyclotomicLayer K) := by sorry
