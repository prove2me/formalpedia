-- Prove2me | Theorems.Thm_GlobalTheory_NormValuation_exponent_relNorm_prime
-- name    : GlobalTheory.NormValuation.exponent_relNorm_prime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:26.832518+00:00
-- url     : https://prove2.me/theorems/21570a98-1401-4b3b-b0f9-9e373e760548
-- title:
--   Norm Valuation: exponent rel Norm prime
-- statement:
--   The Norm Valuation construction uses the exponent rel Norm prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L51-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L51-L76

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

theorem GlobalTheory.NormValuation.exponent_relNorm_prime (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (p : Ideal (𝓞 K)) [p.IsPrime] (hp : p ≠ ⊥) :
    (exponent v (Ideal.relNorm (𝓞 E) p) : ℤ) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * (exponent w p : ℤ) := by sorry
