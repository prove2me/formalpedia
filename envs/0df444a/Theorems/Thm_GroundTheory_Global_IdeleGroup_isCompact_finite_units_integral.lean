-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_finite_units_integral
-- name    : GroundTheory.Global.IdeleGroup.isCompact_finite_units_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:32.435821+00:00
-- url     : https://prove2.me/theorems/ea5557ff-b9b9-4edb-9af9-2778fbfde781
-- title:
--   Idele Group: is Compact finite units integral
-- statement:
--   The Idele Group construction uses the is Compact finite units integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L69-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L69-L81

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.isCompact_finite_units_integral :
    IsCompact {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
      (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K} := by sorry
