-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integers
-- name    : GroundTheory.Global.coe_decomposition_smul_integers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:38:06.268165+00:00
-- url     : https://prove2.me/theorems/f5645105-2e32-504a-92fc-682e0ec2d3dc
-- title:
--   Global: coe decomposition smul integers
-- statement:
--   The Global construction uses the coe decomposition smul integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L121-L124

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

theorem GroundTheory.Global.coe_decomposition_smul_integers (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletionIntegers L) :
    ((σ • x : w.adicCompletionIntegers L) : w.adicCompletion L) = σ • (x : w.adicCompletion L) := by sorry

attribute [defeq] GroundTheory.Global.coe_decomposition_smul_integers
