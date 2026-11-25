-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsSubquotient_exists_piece
-- name    : GroundTheory.Automorphic.IsSubquotient.exists_piece
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:26.641403+00:00
-- url     : https://prove2.me/theorems/759889a9-5371-4c23-a7eb-968e8a8e6266
-- title:
--   Is Subquotient: exists piece
-- statement:
--   The Is Subquotient construction uses the exists piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L90-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L90-L179

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}

theorem GroundTheory.Automorphic.IsSubquotient.exists_piece [π.IsIrreducible] (h : IsSubquotient π ρ) {k : ℕ}
    (Vf : ℕ → Submodule ℂ V) (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ g)) (h0 : Vf 0 = ⊥)
    (hk : Vf k = ⊤) {X : Fin k → Type*} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (σ : ∀ j, Representation ℂ G (X j))
    (Ψ : ∀ j : Fin k,
      Representation.IntertwiningMap (ρ.subrepresentation (Vf (j + 1)) (hV (j + 1))) (σ j))
    (hΨ : ∀ (j : Fin k) x, Ψ j x = 0 ↔ (x : V) ∈ Vf j) :
    ∃ j, IsSubquotient π (σ j) := by sorry
