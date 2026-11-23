-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_adjoin_restricted_sections_of_local
-- name    : GlobalTheory.T.mem_adjoin_restricted_sections_of_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:14.988155+00:00
-- url     : https://prove2.me/theorems/9953554e-3703-479f-89d0-68e4b7c9fa59
-- title:
--   T: mem adjoin restricted sections of local
-- statement:
--   The T construction uses the mem adjoin restricted sections of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemAdjoinRestrictedSectionsOfLocalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemAdjoinRestrictedSectionsOfLocalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_adjoin_restricted_sections_of_local : ∀ (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W)), (∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T) → ∀ W' : X.Opens, IsAffineOpen W' → ∀ (hW : W' ≤ W) (hV : W' ≤ V), (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by sorry
