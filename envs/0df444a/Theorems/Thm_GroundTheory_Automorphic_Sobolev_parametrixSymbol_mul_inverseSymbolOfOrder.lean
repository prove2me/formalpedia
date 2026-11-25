-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_mul_inverseSymbolOfOrder
-- name    : GroundTheory.Automorphic.Sobolev.parametrixSymbol_mul_inverseSymbolOfOrder
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:51.371059+00:00
-- url     : https://prove2.me/theorems/fa328345-7aa9-51ea-ad47-aa9e21055af8
-- title:
--   Sobolev: parametrix Symbol mul inverse Symbol Of Order
-- statement:
--   The Sobolev construction uses the parametrix Symbol mul inverse Symbol Of Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L97-L99

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)

theorem GroundTheory.Automorphic.Sobolev.parametrixSymbol_mul_inverseSymbolOfOrder {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (ξ : E) :
    symb0 c w ξ * qNSymb c w μ N ξ = 1 - rNSymb c w μ N ξ := by sorry
