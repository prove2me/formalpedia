-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_whisker_range
-- name    : GlobalTheory.SecAff.whisker_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:45:36.455287+00:00
-- url     : https://prove2.me/theorems/c75e6f93-1c44-4bc8-ae9c-48a22e3aff09
-- title:
--   Sec Aff: whisker range
-- statement:
--   The Sec Aff construction uses the whisker range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L421-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L421-L438

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
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
omit [GrpObj A]

theorem GlobalTheory.SecAff.whisker_range (h : T' ⟶ T) [IsOpenImmersion h.left] [IsOpenImmersion (h ▷ A).left]
    (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r) :
    (h ▷ A).left.opensRange =
      (T ⊗ A).left.basicOpen (pa (fst T A).left (V := ⊤) (le_pre_top _) r) := by sorry
