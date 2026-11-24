-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_root
-- name    : GlobalTheory.UnitLemma.UnrExt.exists_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:28.400234+00:00
-- url     : https://prove2.me/theorems/d71db1d2-66e2-49c4-9954-a9f445dcc5dc
-- title:
--   Unr Ext: exists root
-- statement:
--   The Unr Ext construction uses the exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L64-L76

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

theorem GlobalTheory.UnitLemma.UnrExt.exists_root [IsAdicComplete (maximalIdeal W) W] (hv : Function.Surjective v) (f : W[X]) (hf : f.Monic)
    (hsep : (f.map v).Separable) (a : k) (ha : (f.map v).eval a = 0) : ∃ w, f.eval w = 0 ∧ v w = a := by sorry
