-- Prove2me | Theorems.Thm_GlobalTheory_exists_torsion_fieldExt
-- name    : GlobalTheory.exists_torsion_fieldExt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:15.464955+00:00
-- url     : https://prove2.me/theorems/25ca4304-5e91-4381-a57d-f80baa61e925
-- title:
--   Global Theory: exists torsion field Ext
-- statement:
--   The Global Theory construction uses the exists torsion field Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsTorsionFieldExt.lean#L12-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsTorsionFieldExt.lean#L12-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsTorsionFieldExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.exists_torsion_fieldExt : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (k k' : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field k'] [IsAlgClosed k'] (j : k →+* k') (t : Sp k ⟶ S), ∃ r : (Over.mk t ⟶ P.A) →* (Over.mk (spMap j ≫ t) ⟶ P.A), (∀ x, (r x).left = spMap j ≫ x.left) ∧ Function.Injective r ∧ (∀ (n : ℕ) y, 0 < n → y ^ n = 1 → ∃ x, r x = y) ∧ ∀ (n : ℕ) x y (c : kˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → (Out.WeilIs P.A P.L n x y (unitOn c) ↔ Out.WeilIs P.A P.L n (r x) (r y) (unitOn (Units.map j.toMonoidHom c))) := by sorry
