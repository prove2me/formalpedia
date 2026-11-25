-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_funPermRep
-- name    : GroundTheory.Global.cycHerbrand_funPermRep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:14.795228+00:00
-- url     : https://prove2.me/theorems/c85f08f4-44a1-4b70-b01a-4d232d4e92bf
-- title:
--   Global: cyc Herbrand fun Perm Rep
-- statement:
--   The Global construction uses the cyc Herbrand fun Perm Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsPerm.lean#L52-L57

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

theorem GroundTheory.Global.cycHerbrand_funPermRep [Fintype G] [Finite X] [Fintype (orbitRel.Quotient G X)] {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (funPermRep ℤ G X) σ =
      ∏ ω : orbitRel.Quotient G X, (Nat.card (stabilizer G (Quotient.out ω)) : ℚ) := by sorry
