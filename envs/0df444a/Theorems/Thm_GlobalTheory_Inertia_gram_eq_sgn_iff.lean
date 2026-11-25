-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_gram_eq_sgn_iff
-- name    : GlobalTheory.Inertia.gram_eq_sgn_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:31.807372+00:00
-- url     : https://prove2.me/theorems/563a9d4a-0abe-4f5b-97a7-3bda5d97849a
-- title:
--   Inertia: gram eq sgn iff
-- statement:
--   The Inertia construction uses the gram eq sgn iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L454-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L454-L460

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Inertia.gram_eq_sgn_iff (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hG0 : G.det ≠ 0) (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex (G.map τ) := by sorry
