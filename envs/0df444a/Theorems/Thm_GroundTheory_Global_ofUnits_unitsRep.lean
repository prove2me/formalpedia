-- Prove2me | Theorems.Thm_GroundTheory_Global_ofUnits_unitsRep
-- name    : GroundTheory.Global.ofUnits_unitsRep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:58:25.796364+00:00
-- url     : https://prove2.me/theorems/c89ae738-af42-41f0-8996-e4c1c1bcdb29
-- title:
--   Global: of Units units Rep
-- statement:
--   The Global construction uses the of Units units Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L90-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L90-L97

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

theorem GroundTheory.Global.ofUnits_unitsRep (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) (g : L ≃ₐ[K] L)
    (u : Additive (𝓞 L)ˣ) :
    (SUnit.ofUnits S).toAdditive (unitsRep K L g u) =
      sUnitRep S hS g ((SUnit.ofUnits S).toAdditive u) := by sorry
