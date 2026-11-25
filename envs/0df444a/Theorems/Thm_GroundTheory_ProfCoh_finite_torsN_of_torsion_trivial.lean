-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_of_torsion_trivial
-- name    : GroundTheory.ProfCoh.finite_torsN_of_torsion_trivial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:02.254275+00:00
-- url     : https://prove2.me/theorems/1f8cd457-bced-4967-8ea9-3e514fb0faea
-- title:
--   Prof Coh: finite tors N of torsion trivial
-- statement:
--   The Prof Coh construction uses the finite tors N of torsion trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L165-L169

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing

theorem GroundTheory.ProfCoh.finite_torsN_of_torsion_trivial {A : Type*} [AddCommGroup A] {n : ℕ}
    (h : ∀ a : A, n • a = 0 → a = 0) : Finite (TorsN A n) := by sorry
