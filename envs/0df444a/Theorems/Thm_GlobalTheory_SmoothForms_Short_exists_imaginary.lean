-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Short_exists_imaginary
-- name    : GlobalTheory.SmoothForms.Short.exists_imaginary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:00.555337+00:00
-- url     : https://prove2.me/theorems/f1c93d26-66a3-4e13-b695-f96aebad8345
-- title:
--   Short: exists imaginary
-- statement:
--   The Short construction uses the exists imaginary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L124-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L124-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short

theorem GlobalTheory.SmoothForms.Short.exists_imaginary (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ star δ = -δ := by sorry
