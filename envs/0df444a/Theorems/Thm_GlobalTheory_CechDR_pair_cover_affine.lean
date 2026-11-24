-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_pair_cover_affine
-- name    : GlobalTheory.CechDR.pair_cover_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:53.06554+00:00
-- url     : https://prove2.me/theorems/f53388b0-28d1-4d39-ae47-d9069ad921b6
-- title:
--   Cech DR: pair cover affine
-- statement:
--   The Cech DR construction uses the pair cover affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairCoverAffine.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PairCoverAffine.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PairCoverAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.pair_cover_affine {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u := by sorry
