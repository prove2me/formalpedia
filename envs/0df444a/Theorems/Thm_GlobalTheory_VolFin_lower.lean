-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_lower
-- name    : GlobalTheory.VolFin.lower
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:50:52.682806+00:00
-- url     : https://prove2.me/theorems/b1a8bf69-a20f-415a-8dd0-2e43a272ca2e
-- title:
--   Vol Fin: lower
-- statement:
--   The Vol Fin construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L162-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L162-L226

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

theorem GlobalTheory.VolFin.lower {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hR : ∀ i, ∀ a ∈ R i, algebraMap F F' a ∈ R' i)
    (hS : ∀ i, ∀ t : F', ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a)
    (hfin : ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e)) :
    ∃ c, ∀ e, Module.Finite K (piece R γ e) → finrank F F' * finrank K (piece R γ e) ≤
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) (e + c)) := by sorry
