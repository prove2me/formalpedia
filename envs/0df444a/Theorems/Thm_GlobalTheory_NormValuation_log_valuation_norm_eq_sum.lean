-- Prove2me | Theorems.Thm_GlobalTheory_NormValuation_log_valuation_norm_eq_sum
-- name    : GlobalTheory.NormValuation.log_valuation_norm_eq_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:36:17.48611+00:00
-- url     : https://prove2.me/theorems/e53b763c-515f-402e-9f77-0bbca3270566
-- title:
--   Norm Valuation: log valuation norm eq sum
-- statement:
--   The Norm Valuation construction uses the log valuation norm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L149-L150

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section

theorem GlobalTheory.NormValuation.log_valuation_norm_eq_sum : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by sorry
