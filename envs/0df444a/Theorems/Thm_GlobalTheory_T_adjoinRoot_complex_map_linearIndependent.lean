-- Prove2me | Theorems.Thm_GlobalTheory_T_adjoinRoot_complex_map_linearIndependent
-- name    : GlobalTheory.T.adjoinRoot_complex_map_linearIndependent
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:14.639227+00:00
-- url     : https://prove2.me/theorems/83484bfb-0102-4142-80a9-6db2380f28c4
-- title:
--   T: adjoin Root complex map linear Independent
-- statement:
--   The T construction uses the adjoin Root complex map linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinRootMapComplexLinearIndependentStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinRootMapComplexLinearIndependentStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.adjoinRoot_complex_map_linearIndependent : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic → ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))), (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧ (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧ ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e → LinearIndependent ℂ (fun j => τ (e j)) := by sorry
