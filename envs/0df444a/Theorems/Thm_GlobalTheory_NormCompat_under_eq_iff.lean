-- Prove2me | Theorems.Thm_GlobalTheory_NormCompat_under_eq_iff
-- name    : GlobalTheory.NormCompat.under_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:24.522085+00:00
-- url     : https://prove2.me/theorems/2b814e58-0617-4448-86dd-afbc52b209cf
-- title:
--   Norm Compat: under eq iff
-- statement:
--   The Norm Compat construction uses the under eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdLocalValuesGlobalOverPlacesAbove.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ProdLocalValuesGlobalOverPlacesAbove.lean#L59-L64

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

theorem GlobalTheory.NormCompat.under_eq_iff {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 E)) :
    w.under (𝓞 E) = v ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by sorry
