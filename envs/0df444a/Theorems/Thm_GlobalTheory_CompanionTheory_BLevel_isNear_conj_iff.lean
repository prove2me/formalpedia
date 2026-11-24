-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isNear_conj_iff
-- name    : GlobalTheory.CompanionTheory.BLevel.isNear_conj_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:57.116207+00:00
-- url     : https://prove2.me/theorems/bfe9a472-fa1d-4d80-829e-86085eb3689b
-- title:
--   BLevel: is Near conj iff
-- statement:
--   The BLevel construction uses the is Near conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L209-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L209-L223

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n m : ℕ}
  (b : Module.Basis (Fin m) L (Fin n → L))
variable {b} {Λ : AddSubgroup (Fin n → L)}

theorem GlobalTheory.CompanionTheory.BLevel.isNear_conj_iff (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : π ≠ 0)
    (A : Matrix (Fin n) (Fin n) L) :
    IsNear ‖π‖ (conj b A) ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, A *ᵥ x - x = π • y := by sorry
