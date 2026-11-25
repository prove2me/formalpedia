-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_globalGenerator_div_baseUnit_eq_generic
-- name    : GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:39.59838+00:00
-- url     : https://prove2.me/theorems/a8b4a211-d110-47cc-b044-3ca5dfae1f95
-- title:
--   T: exists global Generator div base Unit eq generic
-- statement:
--   The T construction uses the exists global Generator div base Unit eq generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalGeneratorDivBaseUnitEqGenericStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlobalGeneratorDivBaseUnitEqGenericStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalGeneratorDivBaseUnitEqGeneric
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalGeneratorDivBaseUnitEqGenericStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K), φ ≫ X.hom = p ≫ spMap (algebraMap R K) → ∀ (M : LB X.left) (c : LB.Gen (M.pull φ)) (a : Kˣ) (b : Rˣ), algebraMap R K (b : R) = (a : K) → ∀ (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val) → ∃ r' : LB.Gen M, r'.IsGen ∧ LB.genPull M r' φ = c := by sorry
