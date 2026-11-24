-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_apply_add_of_mem_perSub
-- name    : GlobalTheory.SW.HaarAlg.apply_add_of_mem_perSub
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:40:43.193882+00:00
-- url     : https://prove2.me/theorems/123b9666-38f9-4434-936f-6f269f9e8edf
-- title:
--   Haar Alg: apply add of mem per Sub
-- statement:
--   The Haar Alg construction uses the apply add of mem per Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L43-L51

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

theorem GlobalTheory.SW.HaarAlg.apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by sorry
