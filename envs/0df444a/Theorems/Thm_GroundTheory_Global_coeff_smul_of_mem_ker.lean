-- Prove2me | Theorems.Thm_GroundTheory_Global_coeff_smul_of_mem_ker
-- name    : GroundTheory.Global.coeff_smul_of_mem_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:44.459825+00:00
-- url     : https://prove2.me/theorems/51497105-5730-4042-a6e7-fbaeaccce362
-- title:
--   Global: coeff smul of mem ker
-- statement:
--   The Global construction uses the coeff smul of mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L120-L125

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
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
open GroundTheory.GroupCoh MulAction
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Finite X] {σ : G}
omit [Fintype G] [Finite X]

theorem GroundTheory.Global.coeff_smul_of_mem_ker (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {f : MonoidAlgebra ℤ X}
    (hf : f ∈ (cycSub (Representation.ofMulAction ℤ G X) σ).ker) (g : G) (x : X) :
    f.coeff (g • x) = f.coeff x := by sorry
