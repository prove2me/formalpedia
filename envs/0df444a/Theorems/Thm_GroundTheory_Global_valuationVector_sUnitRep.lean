-- Prove2me | Theorems.Thm_GroundTheory_Global_valuationVector_sUnitRep
-- name    : GroundTheory.Global.valuationVector_sUnitRep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:58:55.168502+00:00
-- url     : https://prove2.me/theorems/6a1ad9cc-7a7e-47d9-a05b-da2886afaf9c
-- title:
--   Global: valuation Vector s Unit Rep
-- statement:
--   The Global construction uses the valuation Vector s Unit Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L99-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L99-L113

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain NumberField.Units
open scoped Pointwise
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L)))

theorem GroundTheory.Global.valuationVector_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    (g : L ≃ₐ[K] L) (x : Additive (S.unit L)) :
    letI := stableMulAction S hS
    SUnit.valuationVector S (sUnitRep S hS g x) =
      funPermRep ℤ (L ≃ₐ[K] L) S g (SUnit.valuationVector S x) := by sorry
