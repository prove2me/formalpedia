-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_mulOrbit
-- name    : GroundTheory.Global.cycHerbrand_mulOrbit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:15.760365+00:00
-- url     : https://prove2.me/theorems/a9c96476-f9fe-5400-b2ff-637c26c815d2
-- title:
--   Global: cyc Herbrand mul Orbit
-- statement:
--   The Global construction uses the cyc Herbrand mul Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L211-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleHerbrand/Product.lean#L211-L220

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTateNegOneOrbitEquivSymmMk
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleHerbrand_Product
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
noncomputable section
variable {G : Type*} [Group G]
variable {X : Type*} {U : X → Type*} [∀ x, CommGroup (U x)] [MulDistribMulAction G (∀ x, U x)]
variable [MulAction G X]
variable [Fintype G] [MulAction.IsPretransitive G X]

theorem GroundTheory.Global.cycHerbrand_mulOrbit
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ x, U x)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction D (U x₀)) τ := by sorry
