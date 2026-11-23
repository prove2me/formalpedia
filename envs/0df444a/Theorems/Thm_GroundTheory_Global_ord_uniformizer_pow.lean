-- Prove2me | Theorems.Thm_GroundTheory_Global_ord_uniformizer_pow
-- name    : GroundTheory.Global.ord_uniformizer_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:09.496277+00:00
-- url     : https://prove2.me/theorems/3729b9be-b31b-4af7-833e-7be05a4ef9b6
-- title:
--   Global: ord uniformizer pow
-- statement:
--   The Global construction uses the ord uniformizer pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L213-L220

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
variable {n : ℕ}

theorem GroundTheory.Global.ord_uniformizer_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (d : ℕ) : ord ((ϖ : K) ^ d) = d := by sorry
