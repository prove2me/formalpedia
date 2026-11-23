-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isCompact_box
-- name    : GlobalTheory.CompanionTheory.BLevel.isCompact_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:25.392404+00:00
-- url     : https://prove2.me/theorems/31bdc8f9-39c8-4005-9474-b1cece18235d
-- title:
--   BLevel: is Compact box
-- statement:
--   The BLevel construction uses the is Compact box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L158-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L158-L160

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_UpperTheory_Reformulated_B_Qf31_isCompact_box

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
variable [ProperSpace L]

theorem GlobalTheory.CompanionTheory.BLevel.isCompact_box (c : Matrix (Fin m) (Fin m) L) (r : ℝ) :
    IsCompact {g : GL (Fin m) L | (∀ i j, ‖g.1 i j - c i j‖ ≤ r) ∧ ∀ i j, ‖(g⁻¹).1 i j - c i j‖ ≤ r} := by sorry
