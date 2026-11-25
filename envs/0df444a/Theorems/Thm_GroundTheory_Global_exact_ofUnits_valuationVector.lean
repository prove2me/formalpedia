-- Prove2me | Theorems.Thm_GroundTheory_Global_exact_ofUnits_valuationVector
-- name    : GroundTheory.Global.exact_ofUnits_valuationVector
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:30:40.558157+00:00
-- url     : https://prove2.me/theorems/6011560b-d5f0-44e9-97f6-5880f8806ccc
-- title:
--   Global: exact of Units valuation Vector
-- statement:
--   The Global construction uses the exact of Units valuation Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnits.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnits.lean#L40-L46

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
omit [IsGalois K L] [Finite S]

theorem GroundTheory.Global.exact_ofUnits_valuationVector :
    Function.Exact (SUnit.ofUnits (K := L) S).toAdditive
      (SUnit.valuationVector (K := L) S).toAddMonoidHom := by sorry
