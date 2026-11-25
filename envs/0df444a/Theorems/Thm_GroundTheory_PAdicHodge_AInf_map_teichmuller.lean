-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_teichmuller
-- name    : GroundTheory.PAdicHodge.AInf.map_teichmuller
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:34.952675+00:00
-- url     : https://prove2.me/theorems/fcbf96c1-da0b-4856-8f03-19f51ad485cc
-- title:
--   AInf: map teichmuller
-- statement:
--   The AInf construction uses the map teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M]
  [IsUltrametricDist M]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]

theorem GroundTheory.PAdicHodge.AInf.map_teichmuller (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : PreTilt (normInteger K) p) :
    map p φ hφ (WittVector.teichmuller p x) = WittVector.teichmuller p (preTiltMap p φ hφ x) := by sorry
