-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_norm_mulVec_entry
-- name    : GlobalTheory.CompanionTheory.BLevel.norm_mulVec_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:51.497816+00:00
-- url     : https://prove2.me/theorems/dba54aa4-79c3-4dab-ac0e-d9615b74cadc
-- title:
--   BLevel: norm mul Vec entry
-- statement:
--   The BLevel construction uses the norm mul Vec entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L30-L34

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

theorem GlobalTheory.CompanionTheory.BLevel.norm_mulVec_entry {B : Matrix (Fin m) (Fin m) L} {v : Fin m → L} {r : ℝ} (hr : 0 ≤ r)
    (hB : ∀ i j, ‖B i j‖ ≤ r) (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin m) : ‖(B *ᵥ v) i‖ ≤ r := by sorry
