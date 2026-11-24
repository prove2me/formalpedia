-- Prove2me | Theorems.Thm_GlobalTheory_faithfullyFlat_app_of_isAffineHom_flat_surjective
-- name    : GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:18.459065+00:00
-- url     : https://prove2.me/theorems/88de9e59-153f-4ad7-a210-2aee2bbf4181
-- title:
--   Global Theory: faithfully Flat app of is Affine Hom flat surjective
-- statement:
--   The Global Theory construction uses the faithfully Flat app of is Affine Hom flat surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FaithfullyFlatAppOfIsAffineHomFlatSurjective.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FaithfullyFlatAppOfIsAffineHomFlatSurjective.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FaithfullyFlatAppOfIsAffineHomFlatSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective :
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p →
      IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by sorry
