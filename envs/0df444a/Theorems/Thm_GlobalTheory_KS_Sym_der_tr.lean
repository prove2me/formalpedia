-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_der_tr
-- name    : GlobalTheory.KS.Sym.der_tr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:39.970271+00:00
-- url     : https://prove2.me/theorems/0d5eaee6-1437-4898-b8fb-ca39227c6a30
-- title:
--   Sym: der tr
-- statement:
--   The Sym construction uses the der tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L269-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L269-L285

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

theorem GlobalTheory.KS.Sym.der_tr {q : Y ⟶ Sp K} {s : X₂ ⟶ Sp R} {m : Y ⟶ X₂} {D : R → K} {W : X₂.Opens}
    {d : ∀ O : X₂.Opens, Γ(X₂, O) → Γ(Y, m ⁻¹ᵁ O)} (hd : LocDerK q s m D W d) (p : Z ⟶ Y) (π : X₂ ⟶ X)
    {h : Z ⟶ X} (hh : h = p ≫ m ≫ π) {T : Z.Opens} (hT : T ≤ p ⁻¹ᵁ m ⁻¹ᵁ W) : Der h T (tr p m π W d) := by sorry
