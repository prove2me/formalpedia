-- Prove2me | Theorems.Thm_GroundTheory_Global_map_powMonoidHom_unitFiltration
-- name    : GroundTheory.Global.map_powMonoidHom_unitFiltration
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:29.103018+00:00
-- url     : https://prove2.me/theorems/a1657d1a-fed3-4e7b-bcad-4873d14a4cbe
-- title:
--   Global: map pow Monoid Hom unit Filtration
-- statement:
--   The Global construction uses the map pow Monoid Hom unit Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L170-L176

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
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
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd

theorem GroundTheory.Global.map_powMonoidHom_unitFiltration :
    (unitFiltration K (d + 1)).map (powMonoidHom n) = unitFiltration K (d + 1 + d) := by sorry
