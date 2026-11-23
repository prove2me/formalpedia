-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_mem_span_of_frac
-- name    : GlobalTheory.VolFin.mem_span_of_frac
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:54.280271+00:00
-- url     : https://prove2.me/theorems/92f225b8-9965-4930-aae4-4174ecf56c63
-- title:
--   Vol Fin: mem span of frac
-- statement:
--   The Vol Fin construction uses the mem span of frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L117-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L117-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TendstoOfSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.VolFin
open Module Filter Topology
variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}
variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]
omit [IsScalarTower K F F'] [Module.Finite F F']

theorem GlobalTheory.VolFin.mem_span_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    (halg : ∀ b ∈ S, IsAlgebraic F b) (t : F') : t ∈ Submodule.span F (S : Set F') := by sorry
