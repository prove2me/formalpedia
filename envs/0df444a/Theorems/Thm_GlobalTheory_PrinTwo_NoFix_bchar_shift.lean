-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_NoFix_bchar_shift
-- name    : GlobalTheory.PrinTwo.NoFix.bchar_shift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:43.52438+00:00
-- url     : https://prove2.me/theorems/a3c6734d-ca54-4f5d-848a-80a939bc058a
-- title:
--   No Fix: bchar shift
-- statement:
--   The No Fix construction uses the bchar shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L23-L32

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

theorem GlobalTheory.PrinTwo.NoFix.bchar_shift (μ₁ μ₂ : kˣ →* ℂˣ) (a d t : kˣ) :
    bchar μ₁ μ₂ (a * t) (d * t⁻¹) = bchar μ₁ μ₂ a d * ((μ₁ t * absPow k 1 t / μ₂ t : ℂˣ) : ℂ) := by sorry
