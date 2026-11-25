-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_mulEquiv
-- name    : GroundTheory.Global.cycHerbrand_eq_of_mulEquiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:36.016804+00:00
-- url     : https://prove2.me/theorems/a17f92b1-86fa-452e-85ef-cbc3b1fbed16
-- title:
--   Global: cyc Herbrand eq of mul Equiv
-- statement:
--   The Global construction uses the cyc Herbrand eq of mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L42-L52

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {k H G V W : Type*} [CommRing k] [Group H] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ' : Representation k H V} {ρ : Representation k G W}
variable [Fintype H] [Fintype G]

theorem GroundTheory.Global.cycHerbrand_eq_of_mulEquiv (e : H ≃* G) (f : V ≃+ W)
    (hf : ∀ h x, f (ρ' h x) = ρ (e h) (f x)) (τ : H) :
    (HasHerbrandQuotient (cycSubOne ρ' τ) (cycNorm ρ') ↔
      HasHerbrandQuotient (cycSubOne ρ (e τ)) (cycNorm ρ)) ∧
    cycHerbrand ρ' τ = cycHerbrand ρ (e τ) := by sorry
