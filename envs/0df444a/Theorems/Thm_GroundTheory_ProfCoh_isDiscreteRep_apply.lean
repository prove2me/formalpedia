-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
-- name    : GroundTheory.ProfCoh.isDiscreteRep_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:07.330725+00:00
-- url     : https://prove2.me/theorems/8bc3afd6-9277-4b66-a19e-241e3f1bbdca
-- title:
--   Prof Coh: is Discrete Rep apply
-- statement:
--   The Prof Coh construction uses the is Discrete Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L47-L48

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

theorem GroundTheory.ProfCoh.isDiscreteRep_apply (A : Rep.{w} k G) : isDiscreteRep k G A ↔ IsDiscreteRep A := by sorry
