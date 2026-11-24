-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_MulCompat_inv
-- name    : GlobalTheory.GroupGlue.MulCompat.inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:58.438008+00:00
-- url     : https://prove2.me/theorems/57abeaec-0ced-491f-b070-b911c64927b3
-- title:
--   Mul Compat: inv
-- statement:
--   The Mul Compat construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L108-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
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
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]

theorem GlobalTheory.GroupGlue.MulCompat.inv (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i))
    {i j : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i} {v : S ⟶ 𝒰.X j} (a : Over.mk u ⟶ H i)
    (b : Over.mk v ⟶ H j) (h : a.left ≫ ψ i = b.left ≫ ψ j) : (a⁻¹).left ≫ ψ i = (b⁻¹).left ≫ ψ j := by sorry
