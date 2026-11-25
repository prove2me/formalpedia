-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_law_of_inertia
-- name    : GlobalTheory.Inertia.law_of_inertia
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:59.624859+00:00
-- url     : https://prove2.me/theorems/87669210-e1dc-5309-8371-b4b0f675be68
-- title:
--   Inertia: law of inertia
-- statement:
--   The Inertia construction uses the law of inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L512-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L512-L542

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField

theorem GlobalTheory.Inertia.law_of_inertia :
    (∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ), G.IsHermitian → G.det ≠ 0 →
      (∃! p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ∧
      (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
        Pᵀ * G * P.map conj = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
          p = posIndex G) ∧
      (∀ (P : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ), P.det ≠ 0 →
        Pᵀ * G * P.map conj = diagonal d →
          posIndex G = (Finset.univ.filter fun k => 0 < (d k).re).card) ∧
      IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
        ∀ x ∈ W, x ≠ 0 → 0 < (x ⬝ᵥ G *ᵥ star x).re} (posIndex G) ∧
      (∀ (s : ℕ) (H : Matrix (Fin s) (Fin s) ℂ), H.IsHermitian →
        posIndex (fromBlocks G 0 0 H) = posIndex G + posIndex H ∧
        posIndex (reindex finSumFinEquiv finSumFinEquiv (fromBlocks G 0 0 H)) =
          posIndex G + posIndex H) ∧
      posIndex (-G) = r - posIndex G) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ),
      (∀ (G : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → G.det ≠ 0 →
        ∀ τ : E →+* ℂ,
          (∀ p : ℕ, (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
            FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
              p = posIndex (G.map τ)) ∧
          posIndex (G.map (ComplexEmbedding.conjugate τ)) = posIndex (G.map τ)) ∧
      ∀ (X : FD.Data E r) (τ : E →+* ℂ), posIndex (X.Gm.map τ) = X.p0 := by sorry
