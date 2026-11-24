-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_apply_out_mk
-- name    : GlobalTheory.SW.HaarAlg.apply_out_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:19.497383+00:00
-- url     : https://prove2.me/theorems/acfb50dd-88b3-4203-b4a8-ea24ad2b822a
-- title:
--   Haar Alg: apply out mk
-- statement:
--   The Haar Alg construction uses the apply out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L53-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}

theorem GlobalTheory.SW.HaarAlg.apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by sorry
