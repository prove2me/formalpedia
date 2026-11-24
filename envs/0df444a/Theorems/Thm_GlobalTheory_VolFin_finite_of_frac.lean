-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_finite_of_frac
-- name    : GlobalTheory.VolFin.finite_of_frac
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:50:53.012525+00:00
-- url     : https://prove2.me/theorems/6bba671f-9c7e-4266-81f5-2be0631a11c1
-- title:
--   Vol Fin: finite of frac
-- statement:
--   The Vol Fin construction uses the finite of frac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L134-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L134-L160

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

theorem GlobalTheory.VolFin.finite_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    {n : ℕ} (g : Fin n → F') (hg : ∀ t ∈ S, ∃ w : Fin n → F, t = ∑ l, w l • g l) :
    Module.Finite F F' := by sorry
