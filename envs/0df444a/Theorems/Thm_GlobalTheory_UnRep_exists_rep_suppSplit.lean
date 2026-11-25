-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_rep_suppSplit
-- name    : GlobalTheory.UnRep.exists_rep_suppSplit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:38:24.595103+00:00
-- url     : https://prove2.me/theorems/d080ae0f-8bdf-4309-aba4-7edd16d22eaf
-- title:
--   Un Rep: exists rep supp Split
-- statement:
--   The Un Rep construction uses the exists rep supp Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L191-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L191-L319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
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
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem GlobalTheory.UnRep.exists_rep_suppSplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UnRep.IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (N : ℕ), _root_.GlobalTheory.UnRep.IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)), _root_.GlobalTheory.UnRep.IsUnE c G γ.1 ∧ _root_.GlobalTheory.UnRep.IsUnA c G h.1 ∧ _root_.GlobalTheory.UnRep.IsUnA c G k.1 ∧ g.1 = _root_.GlobalTheory.UnRep.fm F γ.1 * h.1 * k.1 ∧ _root_.GlobalTheory.UnRep.SuppSplit c N h.1 ∧ (∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), ∃ w ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by sorry
