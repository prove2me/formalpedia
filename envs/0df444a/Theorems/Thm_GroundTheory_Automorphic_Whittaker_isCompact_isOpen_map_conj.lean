-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_isOpen_map_conj
-- name    : GroundTheory.Automorphic.Whittaker.isCompact_isOpen_map_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:21.679059+00:00
-- url     : https://prove2.me/theorems/72c4c2ca-3f03-4855-afbd-0540a27076a1
-- title:
--   Whittaker: is Compact is Open map conj
-- statement:
--   The Whittaker construction uses the is Compact is Open map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L177-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L177-L186

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
  [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.Whittaker.isCompact_isOpen_map_conj {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) (h : H) :
    IsCompact ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) ∧
      IsOpen ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) := by sorry
