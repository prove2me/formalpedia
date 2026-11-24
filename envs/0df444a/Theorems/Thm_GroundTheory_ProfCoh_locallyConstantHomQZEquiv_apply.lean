-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_locallyConstantHomQZEquiv_apply
-- name    : GroundTheory.ProfCoh.locallyConstantHomQZEquiv_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:41.970964+00:00
-- url     : https://prove2.me/theorems/3d2728e4-d786-4597-bac3-ff834cb1bc03
-- title:
--   Prof Coh: locally Constant Hom QZEquiv apply
-- statement:
--   The Prof Coh construction uses the locally Constant Hom QZEquiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CharactersDefs.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CharactersDefs.lean#L35-L38

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_CharactersDefs
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
variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
variable {G}

theorem GroundTheory.ProfCoh.locallyConstantHomQZEquiv_apply (χ : locallyConstantHom G (AddCircle (1 : ℚ)))
    (g : Additive G) :
    locallyConstantHomQZEquiv G χ g = QZ.toAddCircle.symm (χ.1 g) := by sorry

attribute [defeq] GroundTheory.ProfCoh.locallyConstantHomQZEquiv_apply
