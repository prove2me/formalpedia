-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_frobenius_apply
-- name    : GroundTheory.LocalField.residueAlgEquiv_frobenius_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:26.720308+00:00
-- url     : https://prove2.me/theorems/958f6c66-b202-5903-a024-8e238943560b
-- title:
--   Local Field: residue Alg Equiv frobenius apply
-- statement:
--   The Local Field construction uses the residue Alg Equiv frobenius apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L187-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L187-L193

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
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
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)

theorem GroundTheory.LocalField.residueAlgEquiv_frobenius_apply (h : ramificationIndex K L = 1) (y : 𝓀[L]) :
    residueAlgEquiv K L (frobenius K L h) y = y ^ Nat.card 𝓀[K] := by sorry
