-- Prove2me | Theorems.Thm_GroundTheory_Global_denseRange_units_prod_pi
-- name    : GroundTheory.Global.denseRange_units_prod_pi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:22.538678+00:00
-- url     : https://prove2.me/theorems/15a03800-1a19-4007-8a22-251dbe541383
-- title:
--   Global: dense Range units prod pi
-- statement:
--   The Global construction uses the dense Range units prod pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApproxUnits.lean#L11-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/WeakApproxUnits.lean#L11-L48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApproxUnits
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
open IsDedekindDomain NumberField Topology
variable {K : Type*} [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

theorem GroundTheory.Global.denseRange_units_prod_pi :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by sorry
