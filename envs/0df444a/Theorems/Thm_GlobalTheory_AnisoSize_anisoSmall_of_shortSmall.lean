-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_anisoSmall_of_shortSmall
-- name    : GlobalTheory.AnisoSize.anisoSmall_of_shortSmall
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:05.972087+00:00
-- url     : https://prove2.me/theorems/42e48e92-9081-4d69-914e-59801d3b8bef
-- title:
--   Aniso Size: aniso Small of short Small
-- statement:
--   The Aniso Size construction uses the aniso Small of short Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L231-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L231-L384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize

theorem GlobalTheory.AnisoSize.anisoSmall_of_shortSmall (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hS : ShortSmall E) : AnisoSmall E := by sorry
