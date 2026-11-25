-- Prove2me | Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_sUnitRep
-- name    : GroundTheory.Global.hasHerbrandQuotient_sUnitRep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:59.160844+00:00
-- url     : https://prove2.me/theorems/9f4e92e0-faa7-5903-a507-5151600348a7
-- title:
--   Global: has Herbrand Quotient s Unit Rep
-- statement:
--   The Global construction uses the has Herbrand Quotient s Unit Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnits.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnits.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
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
open NumberField IsDedekindDomain MulAction Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
variable (S : Set (HeightOneSpectrum (𝓞 L))) [Finite S]
omit [IsGalois K L]

theorem GroundTheory.Global.hasHerbrandQuotient_sUnitRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S)
    {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    GroundTheory.GroupCoh.HasHerbrandQuotient (cycSubOne (sUnitRep S hS) σ) (cycNorm (sUnitRep S hS)) := by sorry
