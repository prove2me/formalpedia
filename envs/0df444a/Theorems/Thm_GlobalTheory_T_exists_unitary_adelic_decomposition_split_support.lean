-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unitary_adelic_decomposition_split_support
-- name    : GlobalTheory.T.exists_unitary_adelic_decomposition_split_support
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:50.3095+00:00
-- url     : https://prove2.me/theorems/244ae6ee-4ad6-4b13-8e9e-a1174d298c8f
-- title:
--   T: exists unitary adelic decomposition split support
-- statement:
--   The T construction uses the exists unitary adelic decomposition split support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupportStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupportStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unitary_adelic_decomposition_split_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)), IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧ (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by sorry
