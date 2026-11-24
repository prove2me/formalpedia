-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_quotient_of_smul_mem
-- name    : GroundTheory.Global.finite_quotient_of_smul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:23.19096+00:00
-- url     : https://prove2.me/theorems/7fbecbe9-92ca-48d0-bcb2-c581d27c3c11
-- title:
--   Global: finite quotient of smul mem
-- statement:
--   The Global construction uses the finite quotient of smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Lattice.lean#L11-L22

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Lattice
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
open GroundTheory.GroupCoh
open scoped TensorProduct

theorem GroundTheory.Global.finite_quotient_of_smul_mem {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by sorry
