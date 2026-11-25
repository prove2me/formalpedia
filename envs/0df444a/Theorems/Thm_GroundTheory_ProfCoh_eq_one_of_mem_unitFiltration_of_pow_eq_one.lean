-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_eq_one_of_mem_unitFiltration_of_pow_eq_one
-- name    : GroundTheory.ProfCoh.eq_one_of_mem_unitFiltration_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:36.817601+00:00
-- url     : https://prove2.me/theorems/68547deb-105e-4101-98a5-cbdc48fd7fea
-- title:
--   Prof Coh: eq one of mem unit Filtration of pow eq one
-- statement:
--   The Prof Coh construction uses the eq one of mem unit Filtration of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean#L86-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean#L86-L101

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe

theorem GroundTheory.ProfCoh.eq_one_of_mem_unitFiltration_of_pow_eq_one {k : ℕ} (hk : e + 1 ≤ k) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K k) (h : u ^ p = 1) : u = 1 := by sorry
