-- Prove2me | Theorems.Thm_GlobalTheory_SecAff_pull_kill
-- name    : GlobalTheory.SecAff.pull_kill
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:19.347815+00:00
-- url     : https://prove2.me/theorems/d7bcb0ea-897c-4cd9-a697-01bac4e681f1
-- title:
--   Sec Aff: pull kill
-- statement:
--   The Sec Aff construction uses the pull kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L447-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean#L447-L460

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

theorem GlobalTheory.SecAff.pull_kill [IsProper A.hom] [IsAffine T.left] (hL : L.IsLB) (h : T' ⟶ T)
    [IsOpenImmersion h.left] (r : Γ(T.left, ⊤)) (hr : h.left.opensRange = T.left.basicOpen r)
    (s : SecM A L a T) (hs : pull A L a h s = 0) : ∃ N : ℕ, r ^ N • s = 0 := by sorry
