-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_pow_mem_unitFiltration
-- name    : GroundTheory.ProfCoh.pow_mem_unitFiltration
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:01.724642+00:00
-- url     : https://prove2.me/theorems/6c448803-1b9b-46ca-a9a8-f5a8a5156f42
-- title:
--   Prof Coh: pow mem unit Filtration
-- statement:
--   The Prof Coh construction uses the pow mem unit Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsPower.lean#L66-L72

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

theorem GroundTheory.ProfCoh.pow_mem_unitFiltration {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ p ∈ unitFiltration K (j + e) := by sorry
