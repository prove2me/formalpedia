-- Prove2me | Theorems.Thm_GlobalTheory_VolFin_upper
-- name    : GlobalTheory.VolFin.upper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:34.228914+00:00
-- url     : https://prove2.me/theorems/550bf6e7-9398-4baa-9f84-af814a7ab8fd
-- title:
--   Vol Fin: upper
-- statement:
--   The Vol Fin construction uses the upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L55-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TendstoOfSandwich.lean#L55-L114

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

theorem GlobalTheory.VolFin.upper {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hG : ∀ i, ∃ (n : ℕ) (g : Fin n → F'), ∀ t ∈ R' i, ∃ w : Fin n → F,
      (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • g l)
    (hfin : ∀ e, Module.Finite K (piece R γ e)) :
    ∃ c, ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) ∧
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) e) ≤
        finrank F F' * finrank K (piece R γ (e + c)) := by sorry
