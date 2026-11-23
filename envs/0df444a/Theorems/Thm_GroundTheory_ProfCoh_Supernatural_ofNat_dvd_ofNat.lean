-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_dvd_ofNat
-- name    : GroundTheory.ProfCoh.Supernatural.ofNat_dvd_ofNat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:48.210709+00:00
-- url     : https://prove2.me/theorems/e41958b3-9ba6-488a-bfb6-e3a9b9812d75
-- title:
--   Supernatural: of Nat dvd of Nat
-- statement:
--   The Supernatural construction uses the of Nat dvd of Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L62-L72

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
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
open GroundTheory.ProfCoh.Supernatural

theorem GroundTheory.ProfCoh.Supernatural.ofNat_dvd_ofNat {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ofNat m ∣ ofNat n ↔ m ∣ n := by sorry
