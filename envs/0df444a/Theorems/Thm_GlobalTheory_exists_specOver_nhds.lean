-- Prove2me | Theorems.Thm_GlobalTheory_exists_specOver_nhds
-- name    : GlobalTheory.exists_specOver_nhds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:45.481611+00:00
-- url     : https://prove2.me/theorems/6300921d-35fc-5805-bae3-68b5fbcfc1b6
-- title:
--   Global Theory: exists spec Over nhds
-- statement:
--   The Global Theory construction uses the exists spec Over nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/IrrelevantLeMapLinearGradedMap.lean#L35-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem GlobalTheory.exists_specOver_nhds (T : Over (Spec (.of R))) {t : T.left} {V : T.left.Opens}
    (ht : t ∈ V) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j.left ⁻¹ᵁ V = ⊤ := by sorry
