-- Prove2me | Theorems.Thm_GlobalTheory_KS_Sym_Der_rsT_dl
-- name    : GlobalTheory.KS.Sym.Der.rsT_dl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:46.164871+00:00
-- url     : https://prove2.me/theorems/0ea970fc-0f4d-4233-8cd0-fd647866fafc
-- title:
--   Der: rs T dl
-- statement:
--   The Der construction uses the rs T dl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L207-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstFnCompSpMap.lean#L207-L212

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

theorem GlobalTheory.KS.Sym.Der.rsT_dl {h : Z ⟶ X} {T : Z.Opens} {δ : ∀ O : X.Opens, Γ(X, O) → ∀ O' : Z.Opens, Γ(Z, O')}
    (a : Der h T δ) (L : LB X) (i j : L.ι) {O' O'' : Z.Opens} (h₀ : O'' ≤ O') (h₁ : O' ≤ T)
    (hi : O' ≤ h ⁻¹ᵁ L.U i) (hj : O' ≤ h ⁻¹ᵁ L.U j) : rsT (dl h L δ i j O') O'' = dl h L δ i j O'' := by sorry
