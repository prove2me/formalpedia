-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_intM_natCast_smul
-- name    : GlobalTheory.SW.HaarAlg.intM_natCast_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:56.976657+00:00
-- url     : https://prove2.me/theorems/50fbcfb1-ff00-435c-9592-4467e1d35ee2
-- title:
--   Haar Alg: int M nat Cast smul
-- statement:
--   The Haar Alg construction uses the int M nat Cast smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L14-L17

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

theorem GlobalTheory.SW.HaarAlg.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by sorry
