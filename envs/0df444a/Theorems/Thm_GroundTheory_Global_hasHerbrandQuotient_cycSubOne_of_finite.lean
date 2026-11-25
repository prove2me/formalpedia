-- Prove2me | Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_cycSubOne_of_finite
-- name    : GroundTheory.Global.hasHerbrandQuotient_cycSubOne_of_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:28:03.849289+00:00
-- url     : https://prove2.me/theorems/433a237d-c54b-4ff1-bb02-567b5c25068e
-- title:
--   Global: has Herbrand Quotient cyc Sub One of finite
-- statement:
--   The Global construction uses the has Herbrand Quotient cyc Sub One of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsExact.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsExact.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
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
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

theorem GroundTheory.Global.hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) := by sorry
