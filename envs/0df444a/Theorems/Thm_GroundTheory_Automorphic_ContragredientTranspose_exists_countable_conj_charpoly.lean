-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_countable_conj_charpoly
-- name    : GroundTheory.Automorphic.ContragredientTranspose.exists_countable_conj_charpoly
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:18.138706+00:00
-- url     : https://prove2.me/theorems/2ea90b0a-a129-40f9-aff7-36ead464fc42
-- title:
--   Contragredient Transpose: exists countable conj charpoly
-- statement:
--   The Contragredient Transpose construction uses the exists countable conj charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L474-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/MatrixSimilarity.lean#L474-L505

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.ContragredientTranspose.exists_countable_conj_charpoly (f : F[X]) :
    ∃ s : Set (GL (Fin n) F), s.Countable ∧ ∀ x : GL (Fin n) F,
      (x : Matrix (Fin n) (Fin n) F).charpoly = f → ∃ y ∈ s, ∃ g : GL (Fin n) F,
        x = g * y * g⁻¹ := by sorry
