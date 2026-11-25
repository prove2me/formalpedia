-- Prove2me | Theorems.Thm_GroundTheory_Global_discreteTopology_principalSubgroup
-- name    : GroundTheory.Global.discreteTopology_principalSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:54.037451+00:00
-- url     : https://prove2.me/theorems/e499ee28-6a22-45e8-96c2-da35521eee4a
-- title:
--   Global: discrete Topology principal Subgroup
-- statement:
--   The Global construction uses the discrete Topology principal Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L24-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Discrete.lean#L24-L44

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

theorem GroundTheory.Global.discreteTopology_principalSubgroup :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by sorry
