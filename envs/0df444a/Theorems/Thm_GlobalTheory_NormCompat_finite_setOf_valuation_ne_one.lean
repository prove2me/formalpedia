-- Prove2me | Theorems.Thm_GlobalTheory_NormCompat_finite_setOf_valuation_ne_one
-- name    : GlobalTheory.NormCompat.finite_setOf_valuation_ne_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:41.255796+00:00
-- url     : https://prove2.me/theorems/cdfc3c28-2e8a-4c44-9751-d5a068e29151
-- title:
--   Norm Compat: finite set Of valuation ne one
-- statement:
--   The Norm Compat construction uses the finite set Of valuation ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdLocalValuesGlobalOverPlacesAbove.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdLocalValuesGlobalOverPlacesAbove.lean#L19-L31

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ProdLocalValuesGlobalOverPlacesAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.NormCompat

theorem GlobalTheory.NormCompat.finite_setOf_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by sorry
