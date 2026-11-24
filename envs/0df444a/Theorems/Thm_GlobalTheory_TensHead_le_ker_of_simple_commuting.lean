-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_le_ker_of_simple_commuting
-- name    : GlobalTheory.TensHead.le_ker_of_simple_commuting
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:49.157696+00:00
-- url     : https://prove2.me/theorems/9e464587-4e59-4a36-ad39-a7340acd43b3
-- title:
--   Tens Head: le ker of simple commuting
-- statement:
--   The Tens Head construction uses the le ker of simple commuting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimple.lean#L111-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimple.lean#L111-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead

theorem GlobalTheory.TensHead.le_ker_of_simple_commuting {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by sorry
