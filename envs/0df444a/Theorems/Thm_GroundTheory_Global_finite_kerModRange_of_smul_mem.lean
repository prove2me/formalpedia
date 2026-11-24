-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_kerModRange_of_smul_mem
-- name    : GroundTheory.Global.finite_kerModRange_of_smul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:12.807803+00:00
-- url     : https://prove2.me/theorems/c23b4cb6-a2c5-4cbf-a758-cd0f9574e7f9
-- title:
--   Global: finite ker Mod Range of smul mem
-- statement:
--   The Global construction uses the finite ker Mod Range of smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L95-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean#L95-L113

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
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
open GroundTheory.GroupCoh

theorem GroundTheory.Global.finite_kerModRange_of_smul_mem {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (f g : A →+ A) {n : ℤ} (hn : n ≠ 0) (h : ∀ x ∈ f.ker, n • x ∈ g.range) :
    Finite (KerModRange f g) := by sorry
