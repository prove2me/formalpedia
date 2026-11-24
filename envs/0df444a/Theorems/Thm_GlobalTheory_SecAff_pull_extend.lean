-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_pull_extend
-- name    : GlobalTheory.SecAff.pull_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:59.920952+00:00
-- url     : https://prove2.me/theorems/c910874d-25cf-4b16-81af-cc5b7708f218
-- title:
--   Sec Aff: pull extend
-- statement:
--   The Sec Aff construction uses the pull extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L462-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L462-L475

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

theorem GlobalTheory.SecAff.pull_extend [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (t : SecM A L a T') : ∃ (N : ℕ) (s : SecM A L a T),
      pull A L a h s = pa h.left (V := ⊤) (le_pre_top _) r ^ N • t := by sorry
