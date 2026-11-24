-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sum_poly_eq_sum_torus
-- name    : GlobalTheory.CuspGL.sum_poly_eq_sum_torus
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:33:25.071383+00:00
-- url     : https://prove2.me/theorems/71196de3-3674-4b6f-8171-a777b4c8e657
-- title:
--   Cusp GL: sum poly eq sum torus
-- statement:
--   The Cusp GL construction uses the sum poly eq sum torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteMonicNatDegree.lean#L35-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteMonicNatDegree.lean#L35-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteMonicNatDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.sum_poly_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ (c : F[X] → ℂ) (l : ℕ), (∀ P : F[X], P.Monic → P.natDegree = n → (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → c P = 0) → ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, c P * star (rootSum θ l P) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((n / (minpoly F α).natDegree : ℕ) : ℂ) * c (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) := by sorry
