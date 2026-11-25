-- Prove2me | Theorems.Thm_GlobalTheory_CurveHomLift_isHolTo_pt
-- name    : GlobalTheory.CurveHomLift.isHolTo_pt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:19.459037+00:00
-- url     : https://prove2.me/theorems/2a4f23b4-b726-4ced-9236-98d3674e638d
-- title:
--   Curve Hom Lift: is Hol To pt
-- statement:
--   The Curve Hom Lift construction uses the is Hol To pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmEllipticCurveHomExistsPureTypeVector.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmEllipticCurveHomExistsPureTypeVector.lean#L40-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_PermutesRefl
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueLinearLiftUniformisedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmEllipticCurveHomExistsPureTypeVector
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
open GlobalTheory GlobalTheory.CurveHomLift
open UniformLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem GlobalTheory.CurveHomLift.isHolTo_pt (C : Curve H) : IsHolTo Set.univ fun z : Fin 1 → ℂ => C.pt (z 0) := by sorry
