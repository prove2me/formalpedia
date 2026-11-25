-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_integerUnitsAddEquiv
-- name    : GroundTheory.Global.coe_integerUnitsAddEquiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:27:18.1449+00:00
-- url     : https://prove2.me/theorems/36508adf-2eef-5691-95bc-6756b702af8d
-- title:
--   Global: coe integer Units Add Equiv
-- statement:
--   The Global construction uses the coe integer Units Add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L214-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L214-L217

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

theorem GroundTheory.Global.coe_integerUnitsAddEquiv (x : Additive (w.adicCompletionIntegers L)ˣ) :
    ((((integerUnitsAddEquiv w x).toMul : 𝒪[w.adicCompletion L]ˣ) : 𝒪[w.adicCompletion L]) :
      w.adicCompletion L) = ((x.toMul : w.adicCompletionIntegers L) : w.adicCompletion L) := by sorry

attribute [defeq] GroundTheory.Global.coe_integerUnitsAddEquiv
