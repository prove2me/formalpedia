-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_map_frobeniusEquiv_symm
-- name    : GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_symm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:33.723807+00:00
-- url     : https://prove2.me/theorems/48920775-91c5-5d1a-a0b9-c3df7d9d7ded
-- title:
--   AInf: map frobenius Equiv symm
-- statement:
--   The AInf construction uses the map frobenius Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L69-L74

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

theorem GroundTheory.PAdicHodge.AInf.map_frobeniusEquiv_symm (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) :
    map p φ hφ ((WittVector.frobeniusEquiv p _).symm x) =
      (WittVector.frobeniusEquiv p _).symm (map p φ hφ x) := by sorry
