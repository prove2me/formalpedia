-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_invol_eq_pow
-- name    : GlobalTheory.UnitLemma.UnrExt.invol_eq_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:12.313843+00:00
-- url     : https://prove2.me/theorems/5e48100f-ce5c-4051-9fbd-1867ed983a3a
-- title:
--   Unr Ext: invol eq pow
-- statement:
--   The Unr Ext construction uses the invol eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L11-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedOddDegreeQuadraticLocalExt.lean#L11-L50

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

theorem GlobalTheory.UnitLemma.UnrExt.invol_eq_pow {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] {q : ℕ}
    (hq : Nat.card k = q ^ 2) (s : k ≃+* k) (hss : ∀ x, s (s x) = x) (hne : ∃ x, s x ≠ x) :
    (∃ f, q = p ^ f) ∧ ∀ x, s x = x ^ q := by sorry
