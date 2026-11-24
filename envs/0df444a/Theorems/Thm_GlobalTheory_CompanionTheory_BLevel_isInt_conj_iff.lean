-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isInt_conj_iff
-- name    : GlobalTheory.CompanionTheory.BLevel.isInt_conj_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:21:36.752811+00:00
-- url     : https://prove2.me/theorems/5e1ca2e5-36b7-46d9-aba3-5770e48f34d1
-- title:
--   BLevel: is Int conj iff
-- statement:
--   The BLevel construction uses the is Int conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L203-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L203-L207

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

theorem GlobalTheory.CompanionTheory.BLevel.isInt_conj_iff (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) (A : Matrix (Fin n) (Fin n) L) :
    IsInt (conj b A) ↔ ∀ x ∈ Λ, A *ᵥ x ∈ Λ := by sorry
