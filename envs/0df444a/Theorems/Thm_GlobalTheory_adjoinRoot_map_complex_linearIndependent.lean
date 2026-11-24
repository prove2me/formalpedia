-- Prove2me | Theorems.Thm_GlobalTheory_adjoinRoot_map_complex_linearIndependent
-- name    : GlobalTheory.adjoinRoot_map_complex_linearIndependent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:09.093109+00:00
-- url     : https://prove2.me/theorems/278468c0-8914-4a11-a348-36812ae4512f
-- title:
--   Global Theory: adjoin Root map complex linear Independent
-- statement:
--   The Global Theory construction uses the adjoin Root map complex linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinRootMapComplexLinearIndependent.lean#L8-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinRootMapComplexLinearIndependent.lean#L8-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open Polynomial

theorem GlobalTheory.adjoinRoot_map_complex_linearIndependent :
    ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic →
      ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))),
        (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧
        (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧
        ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e →
          LinearIndependent ℂ (fun j => τ (e j)) := by sorry
