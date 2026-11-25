-- Prove2me | Theorems.Thm_GlobalTheory_HeightOneHopf_truncated_polynomial
-- name    : GlobalTheory.HeightOneHopf.truncated_polynomial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:27.38738+00:00
-- url     : https://prove2.me/theorems/4f02f3f9-04e8-4566-9552-94ad497267d8
-- title:
--   Height One Hopf: truncated polynomial
-- statement:
--   The Height One Hopf construction uses the truncated polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L61-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfSpanCotangent.lean#L61-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfSpanCotangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.HeightOneHopf

theorem GlobalTheory.HeightOneHopf.truncated_polynomial : TruncatedPolynomialStatement := by sorry
