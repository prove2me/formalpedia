-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_invariant_descends
-- name    : GlobalTheory.LevQuot.invariant_descends
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:07.431094+00:00
-- url     : https://prove2.me/theorems/79d92e5f-45f7-4570-9cfb-6bcf951970bc
-- title:
--   Lev Quot: invariant descends
-- statement:
--   The Lev Quot construction uses the invariant descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L36-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L36-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}

theorem GlobalTheory.LevQuot.invariant_descends (r : X ⟶ Y) [Etale r] [QuasiCompact r] [Surjective r] {Γ : Type} (ρ : Γ → (X ⟶ X))
    (hρ : ∀ g, ρ g ≫ r = r)
    (htr : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Spec (CommRingCat.of k) ⟶ X), y ≫ r = y' ≫ r →
      ∃ g, y' = y ≫ ρ g) (V : Y.Opens) :
    Function.Injective (r.app V).hom ∧ ∀ f : Γ(X, r ⁻¹ᵁ V),
      (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g) ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom := by sorry
