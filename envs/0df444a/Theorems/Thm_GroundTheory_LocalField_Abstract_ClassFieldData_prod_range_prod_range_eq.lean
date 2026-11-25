-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_prod_range_prod_range_eq
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.prod_range_prod_range_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:58.797737+00:00
-- url     : https://prove2.me/theorems/278b706a-9e82-4310-8894-cd4681c89de5
-- title:
--   Class Field Data: prod range prod range eq
-- statement:
--   The Class Field Data construction uses the prod range prod range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L139-L145

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.prod_range_prod_range_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (g D0 : ℕ) :
    ∏ i ∈ Finset.range g, ∏ j ∈ Finset.range D0, f (D0 * i + j) =
      ∏ m ∈ Finset.range (g * D0), f m := by sorry
