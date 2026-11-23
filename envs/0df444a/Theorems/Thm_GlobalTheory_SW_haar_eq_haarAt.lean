-- Prove2me | Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt
-- name    : GlobalTheory.SW.haar_eq_haarAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:16.5918+00:00
-- url     : https://prove2.me/theorems/b1dfe4d4-0245-4e63-9ef8-04f00744a7ce
-- title:
--   SW: haar eq haar At
-- statement:
--   The SW construction uses the haar eq haar At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L153-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
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
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.haar_eq_haarAt : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → haar φ = haarAt R φ ∧ (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by sorry
