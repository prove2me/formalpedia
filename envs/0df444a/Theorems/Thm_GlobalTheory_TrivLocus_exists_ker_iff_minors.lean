-- Prove2me | Theorems.Thm_GlobalTheory_TrivLocus_exists_ker_iff_minors
-- name    : GlobalTheory.TrivLocus.exists_ker_iff_minors
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:13:15.616178+00:00
-- url     : https://prove2.me/theorems/ce2dec33-aedf-4dd4-8a41-2b5957dce4b9
-- title:
--   Triv Locus: exists ker iff minors
-- statement:
--   The Triv Locus construction uses the exists ker iff minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKerIffMinors.lean#L13-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus

theorem GlobalTheory.TrivLocus.exists_ker_iff_minors {K : Type} [Field K] {a b : ℕ} (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔ ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by sorry
