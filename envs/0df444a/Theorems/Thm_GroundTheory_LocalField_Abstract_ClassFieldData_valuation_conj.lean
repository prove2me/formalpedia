-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_conj
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:41.835516+00:00
-- url     : https://prove2.me/theorems/f2f4f137-002e-51bb-9dcd-ca1916c2800d
-- title:
--   Class Field Data: valuation conj
-- statement:
--   The Class Field Data construction uses the valuation conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L192-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L192-L210

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
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
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_conj (σ : G) {K K' : OpenSubgroup G}
    (hK' : (K' : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom)
    (a : fixedModule A (K : Subgroup G)) (b : fixedModule A (K' : Subgroup G))
    (hb : (b : A) = σ • (a : A)) : D.valuation K' b = D.valuation K a := by sorry
