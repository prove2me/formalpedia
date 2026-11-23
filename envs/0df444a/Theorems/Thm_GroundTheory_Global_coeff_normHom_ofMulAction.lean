-- Prove2me | Theorems.Thm_GroundTheory_Global_coeff_normHom_ofMulAction
-- name    : GroundTheory.Global.coeff_normHom_ofMulAction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:24.738315+00:00
-- url     : https://prove2.me/theorems/d2b1600d-bebd-4a00-a502-2cbcbbd42754
-- title:
--   Global: coeff norm Hom of Mul Action
-- statement:
--   The Global construction uses the coeff norm Hom of Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L99-L103

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
variable {G X : Type*} [Group G] [Fintype G] [MulAction G X]

theorem GroundTheory.Global.coeff_normHom_ofMulAction (f : MonoidAlgebra ℤ X) (p : X) :
    (normHom (Representation.ofMulAction ℤ G X) f).coeff p = ∑ g : G, f.coeff (g • p) := by sorry
