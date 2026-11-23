-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_le_cyclotomicLimit
-- name    : GroundTheory.PAdicHodge.cyclotomicLayer_le_cyclotomicLimit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.630887+00:00
-- url     : https://prove2.me/theorems/8adfde16-d25e-444e-ad8c-4047ad5e6059
-- title:
--   PAdic Hodge: cyclotomic Layer le cyclotomic Limit
-- statement:
--   The PAdic Hodge construction uses the cyclotomic Layer le cyclotomic Limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/NormalizedTraceTower.lean#L25-L26

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

theorem GroundTheory.PAdicHodge.cyclotomicLayer_le_cyclotomicLimit (n : ℕ) : cyclotomicLayer K n ≤ cyclotomicLimit K := by sorry
