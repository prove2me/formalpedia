-- Prove2me | Theorems.Thm_GlobalTheory_NormValuation_exponent_relNorm
-- name    : GlobalTheory.NormValuation.exponent_relNorm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:55.718253+00:00
-- url     : https://prove2.me/theorems/819acdb0-c9d3-4fb1-82a7-b07cdf714a5b
-- title:
--   Norm Valuation: exponent rel Norm
-- statement:
--   The Norm Valuation construction uses the exponent rel Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L78-L97

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
open GlobalTheory GlobalTheory.NormValuation
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem GlobalTheory.NormValuation.exponent_relNorm (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (I : Ideal (𝓞 K)) : I ≠ ⊥ →
    (exponent v (Ideal.relNorm (𝓞 E) I) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w I : ℤ) := by sorry
