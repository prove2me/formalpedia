-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_iff
-- name    : GroundTheory.ProfCoh.isDiscreteRep_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:13:34.357817+00:00
-- url     : https://prove2.me/theorems/53b8e0ec-790d-4127-a8f1-f048b3435f5d
-- title:
--   Prof Coh: is Discrete Rep iff
-- statement:
--   The Prof Coh construction uses the is Discrete Rep iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L38-L40

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]

theorem GroundTheory.ProfCoh.isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) := by sorry
