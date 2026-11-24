-- Prove2me | Theorems.Thm_GroundTheory_LocalField_cycHerbrand_eq_of_injective
-- name    : GroundTheory.LocalField.cycHerbrand_eq_of_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:56.639634+00:00
-- url     : https://prove2.me/theorems/ac6f63ba-8fbc-4e4a-a929-297abc053cc5
-- title:
--   Local Field: cyc Herbrand eq of injective
-- statement:
--   The Local Field construction uses the cyc Herbrand eq of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L142-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandCyclic.lean#L142-L160

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]

theorem GroundTheory.LocalField.cycHerbrand_eq_of_injective (i : M →* N) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) [i.range.FiniteIndex] (τ : G) :
    (HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) τ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G N) τ)
        (cycNorm (Representation.ofMulDistribMulAction G N))) ∧
    cycHerbrand (Representation.ofMulDistribMulAction G M) τ =
      cycHerbrand (Representation.ofMulDistribMulAction G N) τ := by sorry
