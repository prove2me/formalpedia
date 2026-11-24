-- Prove2me | Theorems.Thm_GlobalTheory_universallyClosed_of_closed_cover_in_universallyClosed
-- name    : GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:26.10866+00:00
-- url     : https://prove2.me/theorems/bc8ccafe-7d35-40f7-acea-1d25d9ee3043
-- title:
--   Global Theory: universally Closed of closed cover in universally Closed
-- statement:
--   The Global Theory construction uses the universally Closed of closed cover in universally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniversallyClosedOfClosedCoverInUniversallyClose.lean#L6-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniversallyClosedOfClosedCoverInUniversallyClose.lean#L6-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyClose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory

theorem GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by sorry
