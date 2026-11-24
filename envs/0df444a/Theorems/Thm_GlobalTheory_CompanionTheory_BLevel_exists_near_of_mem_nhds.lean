-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_exists_near_of_mem_nhds
-- name    : GlobalTheory.CompanionTheory.BLevel.exists_near_of_mem_nhds
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:38.572515+00:00
-- url     : https://prove2.me/theorems/f4b207fd-712f-4dbe-ab3b-88e4d00a759a
-- title:
--   BLevel: exists near of mem nhds
-- statement:
--   The BLevel construction uses the exists near of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L130-L135

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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}

theorem GlobalTheory.CompanionTheory.BLevel.exists_near_of_mem_nhds {c : Fin m → Fin m → L} {A : Set (Fin m → Fin m → L)} (hA : A ∈ 𝓝 c) :
    ∃ ε > 0, ∀ B : Fin m → Fin m → L, (∀ i j, ‖B i j - c i j‖ ≤ ε) → B ∈ A := by sorry
