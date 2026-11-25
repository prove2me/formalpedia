-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_exists_unramified_ext
-- name    : GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:06.788876+00:00
-- url     : https://prove2.me/theorems/a25a5433-c035-4abe-8e65-0f8b4ce48740
-- title:
--   Unr Ext: exists unramified ext
-- statement:
--   The Unr Ext construction uses the exists unramified ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L284-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L284-L353

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

theorem GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by sorry
