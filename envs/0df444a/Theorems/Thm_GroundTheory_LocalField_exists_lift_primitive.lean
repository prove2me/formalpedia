-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_lift_primitive
-- name    : GroundTheory.LocalField.exists_lift_primitive
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:09.931163+00:00
-- url     : https://prove2.me/theorems/36f9a246-fb8e-48f8-a31e-98a28ebd0e8c
-- title:
--   Local Field: exists lift primitive
-- statement:
--   The Local Field construction uses the exists lift primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L64-L95

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_lift_primitive :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧
      P.natDegree = residueDegree K L ∧ (P.map (residue 𝒪[K])).Separable ∧
      IntermediateField.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by sorry
