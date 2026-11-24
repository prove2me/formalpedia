-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_congS_le_intS
-- name    : GlobalTheory.CompanionTheory.BLevel.congS_le_intS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:25.22346+00:00
-- url     : https://prove2.me/theorems/a5f3ab9f-931e-4bc5-b6a4-35cd2a1a5664
-- title:
--   BLevel: cong S le int S
-- statement:
--   The BLevel construction uses the cong S le int S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L100-L101

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

theorem GlobalTheory.CompanionTheory.BLevel.congS_le_intS {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : congS (L := L) (m := m) r h0 h1 ≤ intS := by sorry
