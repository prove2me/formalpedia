-- Prove2me | Theorems.Thm_GroundTheory_Global_sUnitRep_apply
-- name    : GroundTheory.Global.sUnitRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:00.243744+00:00
-- url     : https://prove2.me/theorems/419b16de-0c79-4c08-a239-0e5b7498591b
-- title:
--   Global: s Unit Rep apply
-- statement:
--   The Global construction uses the s Unit Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L85-L88

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

theorem GroundTheory.Global.sUnitRep_apply (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (x : Additive (S.unit L)) :
    sUnitRep S hS g x = Additive.ofMul (sUnitMap S hS g x.toMul) := by sorry
