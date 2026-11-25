-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_fixedModule_of_smul_eq
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.mem_fixedModule_of_smul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:11.367529+00:00
-- url     : https://prove2.me/theorems/16b3e642-7588-45d9-be1c-1077dd378705
-- title:
--   Class Field Data: mem fixed Module of smul eq
-- statement:
--   The Class Field Data construction uses the mem fixed Module of smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L33-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L33-L56

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.mem_fixedModule_of_smul_eq [IsDiscreteModule G A] (K : OpenSubgroup G) {φ : G}
    (hφK : φ ∈ (K : Subgroup G)) (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    {w : A} (hw : w ∈ fixedModule A ((K : Subgroup G) ⊓ D.deg.ker)) (hφw : φ • w = w) :
    w ∈ fixedModule A (K : Subgroup G) := by sorry
