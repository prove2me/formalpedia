-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_finsum_translate
-- name    : GlobalTheory.SW.HaarAlg.finsum_translate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:07.189146+00:00
-- url     : https://prove2.me/theorems/4b5cdbf6-45fc-4b58-b903-9fc959bde59f
-- title:
--   Haar Alg: finsum translate
-- statement:
--   The Haar Alg construction uses the finsum translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L84-L91

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

theorem GlobalTheory.SW.HaarAlg.finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by sorry
