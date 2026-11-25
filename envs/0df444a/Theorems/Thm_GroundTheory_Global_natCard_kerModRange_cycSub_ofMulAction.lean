-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_kerModRange_cycSub_ofMulAction
-- name    : GroundTheory.Global.natCard_kerModRange_cycSub_ofMulAction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:03.490805+00:00
-- url     : https://prove2.me/theorems/c0eeb436-c4d0-4efa-8800-99490781bf2a
-- title:
--   Global: nat Card ker Mod Range cyc Sub of Mul Action
-- statement:
--   The Global construction uses the nat Card ker Mod Range cyc Sub of Mul Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L198-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L198-L276

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

theorem GroundTheory.Global.natCard_kerModRange_cycSub_ofMulAction [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (KerModRange (cycSub (Representation.ofMulAction ℤ G X) σ)
      (normHom (Representation.ofMulAction ℤ G X))) =
      ∏ ω : orbitRel.Quotient G X, Nat.card (stabilizer G (Quotient.out ω)) := by sorry
