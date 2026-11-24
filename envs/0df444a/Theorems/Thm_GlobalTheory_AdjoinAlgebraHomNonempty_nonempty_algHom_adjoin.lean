-- Prove2me | Theorems.Thm_GlobalTheory_AdjoinAlgebraHomNonempty_nonempty_algHom_adjoin
-- name    : GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:54:38.890857+00:00
-- url     : https://prove2.me/theorems/7068b141-5188-466d-b7d6-4d395319651a
-- title:
--   Adjoin Algebra Hom Nonempty: nonempty alg Hom adjoin
-- statement:
--   The Adjoin Algebra Hom Nonempty construction uses the nonempty alg Hom adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyAlgHomAdjoin.lean#L5-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyAlgHomAdjoin.lean#L5-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyAlgHomAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AdjoinAlgebraHomNonempty

theorem GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by sorry
