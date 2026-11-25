-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_of_residueDegree_eq_one
-- name    : GroundTheory.LocalField.mem_of_residueDegree_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:41.130921+00:00
-- url     : https://prove2.me/theorems/b5ae8b4c-a09c-5793-a081-9423ec4216f7
-- title:
--   Local Field: mem of residue Degree eq one
-- statement:
--   The Local Field construction uses the mem of residue Degree eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L152-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedHensel.lean#L152-L199

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

theorem GroundTheory.LocalField.mem_of_residueDegree_eq_one (F : IntermediateField K L) (hF : residueDegree F L = 1)
    (P : 𝒪[K][X]) (hP : P.Monic) (γ : 𝒪[L]) (hγ : aeval γ P = 0)
    (hd : IsUnit (aeval γ (derivative P))) : (γ : L) ∈ F := by sorry
