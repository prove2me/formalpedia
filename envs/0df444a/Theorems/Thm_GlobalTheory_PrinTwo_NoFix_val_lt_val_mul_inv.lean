-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_NoFix_val_lt_val_mul_inv
-- name    : GlobalTheory.PrinTwo.NoFix.val_lt_val_mul_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:14.113739+00:00
-- url     : https://prove2.me/theorems/582e9cc2-3962-4e5a-9362-473d6df6f9a0
-- title:
--   No Fix: val lt val mul inv
-- statement:
--   The No Fix construction uses the val lt val mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L34-L40

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

theorem GlobalTheory.PrinTwo.NoFix.val_lt_val_mul_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : kˣ) :
    valuation k (y : k) < valuation k ((y * ϖ⁻¹ : kˣ) : k) := by sorry
