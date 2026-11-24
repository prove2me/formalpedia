-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_span_map_eq_top
-- name    : GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:13:54.569549+00:00
-- url     : https://prove2.me/theorems/3ad29f56-027a-483a-b017-0621f5fbe6c1
-- title:
--   Basis: span map eq top
-- statement:
--   The Basis construction uses the span map eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top (F : C ⥤ CommAlgCat.{0} R) {S S' : C} (u : S ⟶ S') {n : ℕ}
    {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by sorry
