-- Prove2me | Theorems.Thm_GlobalTheory_KS_TangentAt_existsUnique_vector
-- name    : GlobalTheory.KS.TangentAt.existsUnique_vector
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:59.163802+00:00
-- url     : https://prove2.me/theorems/2f323e5d-4f16-49dc-ba72-e3d0d11a1303
-- title:
--   Tangent At: exists Unique vector
-- statement:
--   The Tangent At construction uses the exists Unique vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationUniformisedAbelianVarietyUniqueVec.lean#L158-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationUniformisedAbelianVarietyUniqueVec.lean#L158-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationUniformisedAbelianVarietyUniqueVec
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.TangentAt
variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

theorem GlobalTheory.KS.TangentAt.existsUnique_vector (htan : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (z : Fin g → ℂ)
    (δ : ∀ W : A.left.Opens, Γ(A.left, W) → ℂ) (hδ : PtDer (u.ex z).left δ)
    (hc : ∀ a, δ ⊤ (constFn A.hom ⊤ a) = 0) :
    ∃! w, ∀ O f, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → δ O f = fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w := by sorry
