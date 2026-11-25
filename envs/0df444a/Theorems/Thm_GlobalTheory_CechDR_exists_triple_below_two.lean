-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_exists_triple_below_two
-- name    : GlobalTheory.CechDR.exists_triple_below_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:31.468198+00:00
-- url     : https://prove2.me/theorems/4eb79789-2373-4a3d-ac1a-4d57d5148682
-- title:
--   Cech DR: exists triple below two
-- statement:
--   The Cech DR construction uses the exists triple below two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L229-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L229-L275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairResBijectiveTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite GlobalTheory.CatCoh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.CechDR
open FormExt FormExtJ
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
variable {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
variable (ψ φ)
variable {ψ φ}
variable (ψ φ)

theorem GlobalTheory.CechDR.exists_triple_below_two (s'' : X'' ⟶ Sp R'') : ∀ (t₁ t₂ : (Triple ψ φ)ᵒᵖ) (S : AffOp X''),
    ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₁ ⟶ S) → ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s'').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X'') (u : S ⟶ S'), IsUnit (mp (OAff s'') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
            Nonempty ((cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t₃ ⟶ S') := by sorry
