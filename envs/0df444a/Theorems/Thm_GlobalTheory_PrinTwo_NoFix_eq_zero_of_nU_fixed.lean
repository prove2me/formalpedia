-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_NoFix_eq_zero_of_nU_fixed
-- name    : GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:53.016218+00:00
-- url     : https://prove2.me/theorems/c4650ebf-e04e-5424-9439-1de48a4d5d71
-- title:
--   No Fix: eq zero of n U fixed
-- statement:
--   The No Fix construction uses the eq zero of n U fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramifiedPrincipalSeriesNoInvariant.lean#L84-L86

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

theorem GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 := by sorry
