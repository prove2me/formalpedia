-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_val_map
-- name    : GlobalTheory.UnitLemma.UnrExt.val_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:32.622102+00:00
-- url     : https://prove2.me/theorems/bc061636-cf2b-44e3-b957-9eead9841e11
-- title:
--   Unr Ext: val map
-- statement:
--   The Unr Ext construction uses the val map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L259-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L259-L282

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

theorem GlobalTheory.UnitLemma.UnrExt.val_map {O W E L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field E] [Field L] [Algebra O E] [IsFractionRing O E] [Algebra W L]
    [IsFractionRing W L] (j : O →+* W) (hj : ∀ ϖ : O, Irreducible ϖ → Irreducible (j ϖ)) (φ : E →+* L)
    (hφ : ∀ x, φ (algebraMap O E x) = algebraMap W L (j x)) (x : E) : val W (φ x) = val O x := by sorry
