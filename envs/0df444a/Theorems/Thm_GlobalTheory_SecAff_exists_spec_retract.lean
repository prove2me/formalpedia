-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_exists_spec_retract
-- name    : GlobalTheory.SecAff.exists_spec_retract
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:14.542935+00:00
-- url     : https://prove2.me/theorems/6cdcbf94-a7b7-4ffe-8538-f2e8cb976680
-- title:
--   Sec Aff: exists spec retract
-- statement:
--   The Sec Aff construction uses the exists spec retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L528-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L528-L545

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

theorem GlobalTheory.SecAff.exists_spec_retract {V : S.Opens} [IsAffine T'.left]
    (g : T' ⟶ overRes (T := baseOver S) V) :
    ∃ (R : Type) (_ : CommRing R)
      (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S) V).left)
      (e : baseAt t ⟶ T') (e' : T' ⟶ baseAt t), e' ≫ e = 𝟙 T' ∧ e' ≫ homAt t = g := by sorry
