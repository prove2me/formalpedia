-- Prove2me | Theorems.Thm_GroundTheory_Global_isClosed_principalSubgroup
-- name    : GroundTheory.Global.isClosed_principalSubgroup
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:04.695011+00:00
-- url     : https://prove2.me/theorems/3eb4186b-79ac-4653-955e-edbb7dc07d49
-- title:
--   Global: is Closed principal Subgroup
-- statement:
--   The Global construction uses the is Closed principal Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L46-L49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
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
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) := by sorry
