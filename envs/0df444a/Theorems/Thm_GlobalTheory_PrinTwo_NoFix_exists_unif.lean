-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_NoFix_exists_unif
-- name    : GlobalTheory.PrinTwo.NoFix.exists_unif
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:06.991256+00:00
-- url     : https://prove2.me/theorems/e180d55b-9dc0-44a3-86df-71edc963e072
-- title:
--   No Fix: exists unif
-- statement:
--   The No Fix construction uses the exists unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L16-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramifiedPrincipalSeriesNoInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo
open GlobalTheory GlobalTheory.PrinTwo GlobalTheory.PrinTwo.NoFix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (k)

theorem GlobalTheory.PrinTwo.NoFix.exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by sorry
