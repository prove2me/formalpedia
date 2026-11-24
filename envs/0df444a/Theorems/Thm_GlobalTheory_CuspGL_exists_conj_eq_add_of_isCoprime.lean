-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_conj_eq_add_of_isCoprime
-- name    : GlobalTheory.CuspGL.exists_conj_eq_add_of_isCoprime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:55.321547+00:00
-- url     : https://prove2.me/theorems/a2bb68cb-cb8e-4042-83fc-d8b0948e895d
-- title:
--   Cusp GL: exists conj eq add of is Coprime
-- statement:
--   The Cusp GL construction uses the exists conj eq add of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsConjEqAddOfIsCoprime.lean#L46-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsConjEqAddOfIsCoprime.lean#L46-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.exists_conj_eq_add_of_isCoprime : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    IsCoprime (LinearMap.charpoly (g.restrict hg)) (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) →
    ∀ h ∈ nilRad A, ∃ e : V ≃ₗ[F] V, e.conj g = g + h := by sorry
