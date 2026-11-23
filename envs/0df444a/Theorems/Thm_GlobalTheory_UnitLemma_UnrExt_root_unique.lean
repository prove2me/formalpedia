-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_root_unique
-- name    : GlobalTheory.UnitLemma.UnrExt.root_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:13.847024+00:00
-- url     : https://prove2.me/theorems/ebac376a-3289-48d8-bde1-292a097e9f7f
-- title:
--   Unr Ext: root unique
-- statement:
--   The Unr Ext construction uses the root unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L78-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
variable {W k : Type} [CommRing W] [IsLocalRing W] [Field k] (v : W →+* k)
  (hker : RingHom.ker v = maximalIdeal W)
include hker

theorem GlobalTheory.UnitLemma.UnrExt.root_unique (f : W[X]) (hsep : (f.map v).Separable) {a b : W} (ha : f.eval a = 0) (hb : f.eval b = 0)
    (hab : v a = v b) : a = b := by sorry
