-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_pow_mul_zero_mono
-- name    : GlobalTheory.SecAff.pow_mul_zero_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:02.652093+00:00
-- url     : https://prove2.me/theorems/84128972-b4b0-4c3a-a1e0-5895787ca469
-- title:
--   Sec Aff: pow mul zero mono
-- statement:
--   The Sec Aff construction uses the pow mul zero mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L116-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}

theorem GlobalTheory.SecAff.pow_mul_zero_mono {R : Type} [CommRing R] {a x : R} {m n : ℕ} (h : a ^ m * x = 0)
    (hmn : m ≤ n) : a ^ n * x = 0 := by sorry
