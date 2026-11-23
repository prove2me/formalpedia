-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_congr_mul
-- name    : GlobalTheory.Inertia.congr_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:42.068314+00:00
-- url     : https://prove2.me/theorems/927adada-b83f-4966-843e-a27ae8a6db0f
-- title:
--   Inertia: congr mul
-- statement:
--   The Inertia construction uses the congr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L68-L71

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
variable {n m : Type*} [Fintype n] [Fintype m]

theorem GlobalTheory.Inertia.congr_mul {l : Type*} (G : Matrix n n ℂ) (P : Matrix n m ℂ) (Q : Matrix m l ℂ) :
    (P * Q)ᵀ * G * (P * Q).map conj = Qᵀ * (Pᵀ * G * P.map conj) * Q.map conj := by sorry
