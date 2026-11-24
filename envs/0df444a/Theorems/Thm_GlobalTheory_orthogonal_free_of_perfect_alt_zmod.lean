-- Prove2me | Theorems.Thm_GlobalTheory_orthogonal_free_of_perfect_alt_zmod
-- name    : GlobalTheory.orthogonal_free_of_perfect_alt_zmod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:59.89925+00:00
-- url     : https://prove2.me/theorems/020a5845-4238-4169-8c52-d9dd572cc08d
-- title:
--   Global Theory: orthogonal free of perfect alt zmod
-- statement:
--   The Global Theory construction uses the orthogonal free of perfect alt zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L124-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L124-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
open ZModPerp

theorem GlobalTheory.orthogonal_free_of_perfect_alt_zmod :
    ∀ (N r : ℕ) [NeZero (r * N)] (Γ : Type) [AddCommGroup Γ] [Module (ZMod (r * N)) Γ]
      [Module.Free (ZMod (r * N)) Γ] [Module.Finite (ZMod (r * N)) Γ]
      (e : LinearMap.BilinForm (ZMod (r * N)) Γ), e.IsAlt → Function.Bijective e →
      (∀ H : Submodule (ZMod (r * N)) Γ, e.orthogonal (e.orthogonal H) = H) ∧
      ∀ T : Submodule (ZMod (r * N)) Γ, Module.Free (ZMod (r * N)) T →
        (∃ T', IsCompl T T') ∧ Module.Free (ZMod (r * N)) (e.orthogonal T) ∧
        (∀ t ∈ T, N • t = 0 ↔ ∃ t' ∈ T, t = r • t') ∧
        ∀ a : Γ, (∀ t ∈ T, r • e a t = 0) ↔ ∃ h ∈ e.orthogonal T, r • a = r • h := by sorry
