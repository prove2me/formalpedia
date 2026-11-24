-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_NoFix_isUnram_mul
-- name    : GlobalTheory.PrinTwo.NoFix.isUnram_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:05.784332+00:00
-- url     : https://prove2.me/theorems/57a944f8-c8aa-46a8-ae2d-d5a772d9ac73
-- title:
--   No Fix: is Unram mul
-- statement:
--   The No Fix construction uses the is Unram mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L20-L21

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

theorem GlobalTheory.PrinTwo.NoFix.isUnram_mul {χ ψ : kˣ →* ℂˣ} (h : IsUnram χ) (h' : IsUnram ψ) : IsUnram (χ * ψ) := by sorry
