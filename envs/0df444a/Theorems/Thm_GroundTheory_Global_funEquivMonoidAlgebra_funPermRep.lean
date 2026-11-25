-- Prove2me | Theorems.Thm_GroundTheory_Global_funEquivMonoidAlgebra_funPermRep
-- name    : GroundTheory.Global.funEquivMonoidAlgebra_funPermRep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:09.142654+00:00
-- url     : https://prove2.me/theorems/3bcb0159-d6b6-4639-b726-fa3777ac39fb
-- title:
--   Global: fun Equiv Monoid Algebra fun Perm Rep
-- statement:
--   The Global construction uses the fun Equiv Monoid Algebra fun Perm Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L43-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
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
open MulAction NumberField IsDedekindDomain
open scoped Pointwise
noncomputable section
variable (k G X : Type*) [CommRing k] [Group G] [MulAction G X]
variable {k G X}

theorem GroundTheory.Global.funEquivMonoidAlgebra_funPermRep [Finite X] (g : G) (F : X → ℤ) :
    funEquivMonoidAlgebra (funPermRep ℤ G X g F) =
      Representation.ofMulAction ℤ G X g (funEquivMonoidAlgebra F) := by sorry
