-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_fac_add
-- name    : GlobalTheory.SW.Vac.fac_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:13.586216+00:00
-- url     : https://prove2.me/theorems/1f7b1e16-5f2c-487b-8bfb-e77721122a0b
-- title:
--   Vac: fac add
-- statement:
--   The Vac construction uses the fac add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L196-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L196-L203

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

theorem GlobalTheory.SW.Vac.fac_add {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ} {y y' : Matrix κ ι ℚ × Matrix κ ι ℚ}
    (h : ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2)) (x : Matrix κ ι ℚ) :
    fac ε (y + y') x = fac ε y x * fac ε y' (x - y.2) := by sorry
