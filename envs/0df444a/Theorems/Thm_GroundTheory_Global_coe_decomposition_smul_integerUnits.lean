-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integerUnits
-- name    : GroundTheory.Global.coe_decomposition_smul_integerUnits
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:26:24.132109+00:00
-- url     : https://prove2.me/theorems/188f1600-a449-548a-bcf1-618cd6e7cf2c
-- title:
--   Global: coe decomposition smul integer Units
-- statement:
--   The Global construction uses the coe decomposition smul integer Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L143-L147

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
variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
variable {w}
variable (w)
variable {w}

theorem GroundTheory.Global.coe_decomposition_smul_integerUnits (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (u : (w.adicCompletionIntegers L)ˣ) :
    (((σ • u : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L) :
      w.adicCompletion L) = σ • ((u : w.adicCompletionIntegers L) : w.adicCompletion L) := by sorry

attribute [defeq] GroundTheory.Global.coe_decomposition_smul_integerUnits
