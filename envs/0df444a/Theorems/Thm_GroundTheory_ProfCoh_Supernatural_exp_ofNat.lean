-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
-- name    : GroundTheory.ProfCoh.Supernatural.exp_ofNat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:30.597794+00:00
-- url     : https://prove2.me/theorems/9e0be9b0-44d8-403a-ae0d-1972be2ac4da
-- title:
--   Supernatural: exp of Nat
-- statement:
--   The Supernatural construction uses the exp of Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L54-L54

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

theorem GroundTheory.ProfCoh.Supernatural.exp_ofNat (n : ℕ) (p : Nat.Primes) : (ofNat n).exp p = n.factorization p := by sorry

attribute [defeq] GroundTheory.ProfCoh.Supernatural.exp_ofNat
