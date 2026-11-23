-- Prove2me | Theorems.Thm_GlobalTheory_CuspRep_isOpen_stab_of_mem_nhds
-- name    : GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:26.757842+00:00
-- url     : https://prove2.me/theorems/b794bc77-1864-4627-8957-31e5e6edc172
-- title:
--   Cusp Rep: is Open stab of mem nhds
-- statement:
--   The Cusp Rep construction uses the is Open stab of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/IsOpenStabOfMemNhds.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/IsOpenStabOfMemNhds.lean#L54-L57

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
import Theorems.Thm_UpperTheory_Reformulated_B_IsOpenStabilizer_isOpen_stab_of_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CuspRep

theorem GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (v : V)
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsOpen {g : G | ρ g v = v} := by sorry
