-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_mem_adjoin_eq
-- name    : GlobalTheory.ThK.Dbl.Dens.exists_mem_adjoin_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:36.148634+00:00
-- url     : https://prove2.me/theorems/0f20e0db-9b1c-4a90-be96-aeb591f76faf
-- title:
--   Dens: exists mem adjoin eq
-- statement:
--   The Dens construction uses the exists mem adjoin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L111-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/PairsD.lean#L111-L139

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal

theorem GlobalTheory.ThK.Dbl.Dens.exists_mem_adjoin_eq {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (O : Set (Module.End ℂ V)) (hV : Module.rank ℂ V ≤ ℵ₀)
    (hirr : ∀ N : Submodule ℂ V, (∀ T ∈ O, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ O, ∀ x ∈ s, T x = f x := by sorry
