-- Prove2me | Theorems.Thm_GlobalTheory_T_universallyClosed_of_closed_image_cover
-- name    : GlobalTheory.T.universallyClosed_of_closed_image_cover
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:35.426188+00:00
-- url     : https://prove2.me/theorems/b0229297-b5a6-466e-b7a0-22d0cc1c3a3f
-- title:
--   T: universally Closed of closed image cover
-- statement:
--   The T construction uses the universally Closed of closed image cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniversallyClosedOfClosedCoverInUniversallyCloseStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniversallyClosedOfClosedCoverInUniversallyCloseStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyClose
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniversallyClosedOfClosedCoverInUniversallyCloseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.universallyClosed_of_closed_image_cover : ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y), UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) → π '' T = Set.univ → UniversallyClosed f := by sorry
