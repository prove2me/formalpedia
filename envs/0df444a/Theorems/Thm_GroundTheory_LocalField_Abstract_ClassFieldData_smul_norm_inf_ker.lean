-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_norm_inf_ker
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.smul_norm_inf_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:45:48.92113+00:00
-- url     : https://prove2.me/theorems/bd4da527-b110-44de-8a1f-f015c32a9f05
-- title:
--   Class Field Data: smul norm inf ker
-- statement:
--   The Class Field Data construction uses the smul norm inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L85-L90

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.smul_norm_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) (y : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) y : A) =
      norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨g • (y : A), smul_mem_fixedModule_inf_ker hLK hg y.2⟩ := by sorry
