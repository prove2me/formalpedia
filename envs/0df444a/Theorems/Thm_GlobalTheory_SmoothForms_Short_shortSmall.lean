-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Short_shortSmall
-- name    : GlobalTheory.SmoothForms.Short.shortSmall
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:10.482585+00:00
-- url     : https://prove2.me/theorems/02239884-37f2-435e-be66-5d3cc99bf639
-- title:
--   Short: short Small
-- statement:
--   The Short construction uses the short Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L149-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L149-L354

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

theorem GlobalTheory.SmoothForms.Short.shortSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (hfr : FrameSmall E) : ShortSmall E := by sorry
