-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_hasLevel_mul
-- name    : GlobalTheory.SW.HaarAlg.hasLevel_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:00.494614+00:00
-- url     : https://prove2.me/theorems/3b6d8c42-c991-4d48-806b-dc769d97b6a7
-- title:
--   Haar Alg: has Level mul
-- statement:
--   The Haar Alg construction uses the has Level mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L19-L25

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

theorem GlobalTheory.SW.HaarAlg.hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by sorry
