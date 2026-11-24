-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_fixed_iff
-- name    : GlobalTheory.SW.Vac.fixed_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:25.197326+00:00
-- url     : https://prove2.me/theorems/15a477d3-cc16-47a4-b7f9-23d6dd09ca26
-- title:
--   Vac: fixed iff
-- statement:
--   The Vac construction uses the fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L188-L194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.fixed_iff [DecidableEq ι] (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ)
    (y : Matrix κ ι ℚ × Matrix κ ι ℚ) (w : Matrix κ ι ℚ → ℂ) :
    ε y • heisS y.1 y.2 w = w ↔ ∀ x, fac ε y x * w (x - y.2) = w x := by sorry
