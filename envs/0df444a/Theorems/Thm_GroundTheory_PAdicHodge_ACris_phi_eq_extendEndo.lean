-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_phi_eq_extendEndo
-- name    : GroundTheory.PAdicHodge.ACris.phi_eq_extendEndo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:38.053029+00:00
-- url     : https://prove2.me/theorems/8974adef-3ae8-43f7-8c27-aeab29bb36f1
-- title:
--   ACris: phi eq extend Endo
-- statement:
--   The ACris construction uses the phi eq extend Endo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisGalois.lean#L92-L93

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
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
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.ACris.phi_eq_extendEndo : phi K p = extendEndo (phiZero K p) := by sorry
