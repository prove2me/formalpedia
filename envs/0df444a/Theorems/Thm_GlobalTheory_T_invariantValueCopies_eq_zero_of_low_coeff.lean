-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantValueCopies_eq_zero_of_low_coeff
-- name    : GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:51.824357+00:00
-- url     : https://prove2.me/theorems/c4f45886-68c8-4fbd-b0a6-c4de3f7edf1d
-- title:
--   T: invariant Value Copies eq zero of low coeff
-- statement:
--   The T construction uses the invariant Value Copies eq zero of low coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantValueCopiesEqZeroOfLowCoeffStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/InvariantValueCopiesEqZeroOfLowCoeffStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by sorry
