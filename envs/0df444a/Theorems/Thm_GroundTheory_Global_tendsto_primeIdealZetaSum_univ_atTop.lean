-- Prove2me | Theorems.Thm_GroundTheory_Global_tendsto_primeIdealZetaSum_univ_atTop
-- name    : GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:58.445953+00:00
-- url     : https://prove2.me/theorems/1c7fb69b-445b-4e37-b8ee-082c53e74d4b
-- title:
--   Global: tendsto prime Ideal Zeta Sum univ at Top
-- statement:
--   The Global construction uses the tendsto prime Ideal Zeta Sum univ at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L352-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L352-L368

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem GroundTheory.Global.tendsto_primeIdealZetaSum_univ_atTop :
    Tendsto (fun s => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)
      (𝓝[>] 1) atTop := by sorry
