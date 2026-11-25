-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_prod_pow_div
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.smul_prod_pow_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:36.091981+00:00
-- url     : https://prove2.me/theorems/6349b420-bb71-4e46-bbc7-edc57a377395
-- title:
--   Class Field Data: smul prod pow div
-- statement:
--   The Class Field Data construction uses the smul prod pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L75-L86

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
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
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [((L : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.smul_prod_pow_div (φ : G) (y : A) (n : ℕ) :
    φ • (∏ ν : Fin n, φ ^ (ν : ℕ) • y) / ∏ ν : Fin n, φ ^ (ν : ℕ) • y = φ ^ n • y / y := by sorry
