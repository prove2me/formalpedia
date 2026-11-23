-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
-- name    : GroundTheory.ProfCoh.isOpen_stabilizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:06.430097+00:00
-- url     : https://prove2.me/theorems/5a054cac-a5f1-4c60-bc16-80684671d095
-- title:
--   Prof Coh: is Open stabilizer
-- statement:
--   The Prof Coh construction uses the is Open stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L34-L36

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

theorem GroundTheory.ProfCoh.isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) := by sorry
