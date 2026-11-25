-- Prove2me | Theorems.Thm_GroundTheory_Global_decomposition_smul_def
-- name    : GroundTheory.Global.decomposition_smul_def
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:57:06.640824+00:00
-- url     : https://prove2.me/theorems/e8d93c37-9ff6-4297-9dd0-77ddae1d2dd8
-- title:
--   Global: decomposition smul def
-- statement:
--   The Global construction uses the decomposition smul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L96-L99

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

theorem GroundTheory.Global.decomposition_smul_def (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) :
    σ • x = adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x := by sorry
