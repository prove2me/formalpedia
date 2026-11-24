-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_LocDerK_add_field
-- name    : GlobalTheory.KS.Sym.LocDerK_add_field
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:44:54.098318+00:00
-- url     : https://prove2.me/theorems/20f96164-6adb-4629-84b1-44a888dbc9d8
-- title:
--   Sym: Loc Der K add field
-- statement:
--   The Sym construction uses the Loc Der K add field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L328-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L328-L350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstFnCompSpMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Sym
variable {X X₂ Y Z : Scheme.{0}}
variable {K R : Type} [Field K] [CommRing R]

theorem GlobalTheory.KS.Sym.LocDerK_add_field {g : ℕ} (x₀ : R →+* K) {q : Y ⟶ Sp K} {s : X ⟶ Sp R} {m : Y ⟶ X}
    (sq : m ≫ s = q ≫ spMap x₀) {D : R → K} {W : X.Opens}
    {d : ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (t : Fin g → Γ(Y, m ⁻¹ᵁ W))
    {w : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)} (hw : ∀ a, IsVF q (w a)) :
    LocDerK q s m D W (fun O f => d O f + ∑ a, rsT (t a) _ * w a _ (pbT m f _)) := by sorry
