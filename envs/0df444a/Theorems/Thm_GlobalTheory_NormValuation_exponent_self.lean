-- Prove2me | Theorems.Thm_GlobalTheory_NormValuation_exponent_self
-- name    : GlobalTheory.NormValuation.exponent_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:33.990493+00:00
-- url     : https://prove2.me/theorems/8991fbcd-bce4-4c13-8430-c51e0b891a6e
-- title:
--   Norm Valuation: exponent self
-- statement:
--   The Norm Valuation construction uses the exponent self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IntValuationNormEqSumResidueDegreeMul.lean#L27-L28

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
variable {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R)

theorem GlobalTheory.NormValuation.exponent_self : exponent w w.asIdeal = 1 := by sorry
