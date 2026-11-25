-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_triple_cover_affine
-- name    : GlobalTheory.CechDR.triple_cover_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:07.27831+00:00
-- url     : https://prove2.me/theorems/ea7d0feb-97c0-4512-b553-74f2ff99f687
-- title:
--   Cech DR: triple cover affine
-- statement:
--   The Cech DR construction uses the triple cover affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L186-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechTripleRestrictCompositeInjectiveSecond.lean#L186-L227

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

theorem GlobalTheory.CechDR.triple_cover_affine (s'' : X'' ⟶ Sp R'') : ∀ T : AffOp X'', ∃ (n : ℕ) (b : Fin n → (OAff s'').obj T),
    Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X'') (u : T ⟶ S),
      IsUnit (mp (OAff s'') u (b i)) →
        ∃ (t : (Triple ψ φ)ᵒᵖ) (v : T ⟶ (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t)
          (w : (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ)).obj t ⟶ S), v ≫ w = u := by sorry
