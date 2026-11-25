-- Prove2me | Theorems.Thm_GlobalTheory_ClosureDimensionSpecialization_dim_closure_le_of_specializes
-- name    : GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:36.401827+00:00
-- url     : https://prove2.me/theorems/b0a38ba3-4905-5d67-93cc-fe56f6247ba1
-- title:
--   Closure Dimension Specialization: dim closure le of specializes
-- statement:
--   The Closure Dimension Specialization construction uses the dim closure le of specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DimClosureLeOfSpecializes.lean#L7-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DimClosureLeOfSpecializes.lean#L7-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DimClosureLeOfSpecializes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosureDimensionSpecialization
open Order TopologicalSpace Topology

theorem GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by sorry
