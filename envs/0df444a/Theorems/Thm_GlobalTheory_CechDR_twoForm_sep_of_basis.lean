-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_twoForm_sep_of_basis
-- name    : GlobalTheory.CechDR.twoForm_sep_of_basis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:14:51.408622+00:00
-- url     : https://prove2.me/theorems/cbb9dfdf-d2d0-48da-b004-bee2f28d4b87
-- title:
--   Cech DR: two Form sep of basis
-- statement:
--   The Cech DR construction uses the two Form sep of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L54-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoFormExistsPowSmulEqZeroOfIsLocalization.lean#L54-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoFormExistsPowSmulEqZeroOfIsLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR

theorem GlobalTheory.CechDR.twoForm_sep_of_basis : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R') {C' : Type} [Category.{0} C'], ∀ (G : C' ⥤ AffOp X'), (∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (OAff s').obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S), IsUnit (mp (OAff s') u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (T : AffOp X') (η : Om R' ((OAff s').obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm (OAff s') 2 u η = 0) → η = 0) := by sorry
