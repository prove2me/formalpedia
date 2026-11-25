-- Prove2me | Theorems.Thm_GlobalTheory_TanBasisLocal_coeff_compat
-- name    : GlobalTheory.TanBasisLocal.coeff_compat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:33:38.785383+00:00
-- url     : https://prove2.me/theorems/051e808f-d8df-4045-b698-1127cf95db74
-- title:
--   Tan Basis Local: coeff compat
-- statement:
--   The Tan Basis Local construction uses the coeff compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L96-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem GlobalTheory.TanBasisLocal.coeff_compat {S A B C : Type} [CommRing S] [CommRing A] [CommRing B] [CommRing C] {φ : S →+* A}
    {ψ : S →+* B} {χ : S →+* C} (α : A →+* C) (β : B →+* C) (hα : α.comp φ = χ) (hβ : β.comp ψ = χ)
    {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt x w) (hb : TanBasis (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k))
    {a : Fin m → A} {b : Fin m → B}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w))
    (hb' : IsCombAt (spMap ψ ≫ x) (fun k => spMap (dualMap ψ) ≫ v k) b (spMap (dualMap ψ) ≫ w)) :
    (fun j => α (a j)) = fun j => β (b j) := by sorry
