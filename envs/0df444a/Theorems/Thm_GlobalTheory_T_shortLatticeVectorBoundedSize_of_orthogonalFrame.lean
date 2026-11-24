-- Prove2me | Theorems.Thm_GlobalTheory_T_shortLatticeVectorBoundedSize_of_orthogonalFrame
-- name    : GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:40.80833+00:00
-- url     : https://prove2.me/theorems/3f28575c-e288-4263-8c86-a9dd846c029d
-- title:
--   T: short Lattice Vector Bounded Size of orthogonal Frame
-- statement:
--   The T construction uses the short Lattice Vector Bounded Size of orthogonal Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrameStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrameStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrameStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E → ShortSmall E := by sorry
