-- Prove2me | Theorems.Thm_GlobalTheory_addHom_zmod_pow_algebraMap_mul
-- name    : GlobalTheory.addHom_zmod_pow_algebraMap_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:49.576546+00:00
-- url     : https://prove2.me/theorems/2d3ea3df-5f9d-48ad-99d0-24c6795029b2
-- title:
--   Global Theory: add Hom zmod pow algebra Map mul
-- statement:
--   The Global Theory construction uses the add Hom zmod pow algebra Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsZmodPowCoboundaryOfRationalCoboundary.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsZmodPowCoboundaryOfRationalCoboundary.lean#L71-L88

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsZmodPowCoboundaryOfRationalCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory

theorem GlobalTheory.addHom_zmod_pow_algebraMap_mul (O : Type) [CommRing O] (l m : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (A : O →+ ZMod (l ^ m)) (u : ℤ_[l]) (o : O) :
    A (algebraMap ℤ_[l] O u * o) = PadicInt.toZModPow m u * A o := by sorry
