-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_om_eq
-- name    : GlobalTheory.SW.Vac.om_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:17.061299+00:00
-- url     : https://prove2.me/theorems/437a1a17-dbe1-4462-b786-b031205eabd0
-- title:
--   Vac: om eq
-- statement:
--   The Vac construction uses the om eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L49-L51

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

theorem GlobalTheory.SW.Vac.om_eq (y y' : Matrix κ ι ℚ × Matrix κ ι ℚ) :
    (∑ k, (y.1 k ⬝ᵥ y'.2 k - y'.1 k ⬝ᵥ y.2 k) : ℚ) = pr y.1 y'.2 - pr y'.1 y.2 := by sorry
