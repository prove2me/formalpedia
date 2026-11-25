-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mk_norm_eq_primeNorm
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.mk_norm_eq_primeNorm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:29.65609+00:00
-- url     : https://prove2.me/theorems/8d08fc1b-0fe2-4c16-b6f3-2cc0409413a6
-- title:
--   Class Field Data: mk norm eq prime Norm
-- statement:
--   The Class Field Data construction uses the mk norm eq prime Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L137-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Reciprocity.lean#L137-L152

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
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
  (D : ClassFieldData G A)
variable {D} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.mk_norm_eq_primeNorm (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by sorry
