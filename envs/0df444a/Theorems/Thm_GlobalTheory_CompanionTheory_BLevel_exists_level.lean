-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_exists_level
-- name    : GlobalTheory.CompanionTheory.BLevel.exists_level
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:30.90896+00:00
-- url     : https://prove2.me/theorems/cb31c413-285b-4dfc-ae92-dc3b64d8a1d8
-- title:
--   BLevel: exists level
-- statement:
--   The BLevel construction uses the exists level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L137-L154

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

theorem GlobalTheory.CompanionTheory.BLevel.exists_level {W : Set (GL (Fin m) L)} (hW : W ∈ 𝓝 (1 : GL (Fin m) L)) :
    ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : GL (Fin m) L, IsNear ‖π‖ g.1 → g ∈ W := by sorry
