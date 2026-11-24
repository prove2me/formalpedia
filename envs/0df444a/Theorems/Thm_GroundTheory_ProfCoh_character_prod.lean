-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_character_prod
-- name    : GroundTheory.ProfCoh.character_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:04.444345+00:00
-- url     : https://prove2.me/theorems/c797f56c-5f29-432f-8caf-3975c8c74994
-- title:
--   Prof Coh: character prod
-- statement:
--   The Prof Coh construction uses the character prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeCharacter.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/PermLatticeCharacter.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_PermLatticeCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Module Representation
universe uk uG uU uV uW
variable {k : Type uk} {G : Type uG} [Field k] [Group G]

theorem GroundTheory.ProfCoh.character_prod {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g := by sorry
