-- Prove2me | Theorems.Thm_GlobalTheory_nabValN_eq_sum_coeff
-- name    : GlobalTheory.nabValN_eq_sum_coeff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:36.054552+00:00
-- url     : https://prove2.me/theorems/9cad98c2-d72a-48e0-8fb0-bb30b0e7981b
-- title:
--   Global Theory: nab Val N eq sum coeff
-- statement:
--   The Global Theory construction uses the nab Val N eq sum coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeff.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NabValNEqSumCoeff.lean#L36-L41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff
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
open GlobalTheory

theorem GlobalTheory.nabValN_eq_sum_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by sorry
