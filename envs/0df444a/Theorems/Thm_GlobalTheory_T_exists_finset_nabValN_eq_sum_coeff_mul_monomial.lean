-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_nabValN_eq_sum_coeff_mul_monomial
-- name    : GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:02.63322+00:00
-- url     : https://prove2.me/theorems/f34189ac-09c3-49b7-86a6-8e37e5f6edc3
-- title:
--   T: exists finset nab Val N eq sum coeff mul monomial
-- statement:
--   The T construction uses the exists finset nab Val N eq sum coeff mul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeffStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeffStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeffStatement
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

theorem GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by sorry
