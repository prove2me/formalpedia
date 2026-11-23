-- Prove2me | Theorems.Thm_GlobalTheory_OrbitGrowth_mem_good
-- name    : GlobalTheory.OrbitGrowth.mem_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:08.747542+00:00
-- url     : https://prove2.me/theorems/9a865b35-04b7-462e-a8da-1e0775ef2f99
-- title:
--   Orbit Growth: mem good
-- statement:
--   The Orbit Growth construction uses the mem good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MulApply.lean#L47-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.OrbitGrowth.mem_good {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} :
    x ∈ good A ↔ FiniteDimensional ℂ (orb A x) := by sorry
