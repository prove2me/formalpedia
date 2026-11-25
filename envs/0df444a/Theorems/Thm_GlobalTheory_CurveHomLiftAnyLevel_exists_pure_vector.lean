-- Prove2me | Theorems.Thm_GlobalTheory_CurveHomLiftAnyLevel_exists_pure_vector
-- name    : GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:02:22.986129+00:00
-- url     : https://prove2.me/theorems/968d5c7f-c64b-5d8e-b97e-e4487c8bfcdb
-- title:
--   Curve Hom Lift Any Level: exists pure vector
-- statement:
--   The Curve Hom Lift Any Level construction uses the exists pure vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmCurveHomExistsPureTypeVectorAnyLevel.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmCurveHomExistsPureTypeVectorAnyLevel.lean#L17-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmCurveHomExistsPureTypeVectorAnyLevel
import Theorems.Thm_GlobalTheory_CurveHomLift_exists_pure_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CurveHomLiftAnyLevel
open UniformLift CurveHomLift

theorem GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by sorry
