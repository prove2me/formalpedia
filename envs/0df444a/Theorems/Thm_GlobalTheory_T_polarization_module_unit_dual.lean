-- Prove2me | Theorems.Thm_GlobalTheory_T_polarization_module_unit_dual
-- name    : GlobalTheory.T.polarization_module_unit_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:39.089641+00:00
-- url     : https://prove2.me/theorems/986beca1-8735-46c6-a7ec-0014feb6685f
-- title:
--   T: polarization module unit dual
-- statement:
--   The T construction uses the polarization module unit dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDualStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDualStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDualStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.polarization_module_unit_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by sorry
