-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_map
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:27.301337+00:00
-- url     : https://prove2.me/theorems/b11766ab-f4ce-52b3-8e17-0cc988d91ca1
-- title:
--   AInf: fontaine Theta map
-- statement:
--   The AInf construction uses the fontaine Theta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfGalois.lean#L36-L39

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

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (w : AInf K p) :
    WittVector.fontaineTheta (normInteger L) p (map p φ hφ w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) := by sorry
