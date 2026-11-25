-- Prove2me | Theorems.Thm_GroundTheory_Global_unitsRep_apply
-- name    : GroundTheory.Global.unitsRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:24.090941+00:00
-- url     : https://prove2.me/theorems/4cc7bfea-b2d9-58a4-a10d-aa5e8359bb61
-- title:
--   Global: units Rep apply
-- statement:
--   The Global construction uses the units Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsRep.lean#L40-L42

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
variable [NumberField L]
omit [NumberField L]

theorem GroundTheory.Global.unitsRep_apply (g : L ≃ₐ[K] L) (u : Additive (𝓞 L)ˣ) :
    unitsRep K L g u = Additive.ofMul (unitsMap g u.toMul) := by sorry
