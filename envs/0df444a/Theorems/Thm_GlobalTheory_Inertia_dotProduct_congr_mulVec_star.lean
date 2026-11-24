-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_dotProduct_congr_mulVec_star
-- name    : GlobalTheory.Inertia.dotProduct_congr_mulVec_star
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:29.49186+00:00
-- url     : https://prove2.me/theorems/bb7c8295-c17f-4463-b2fc-3fd764b81d64
-- title:
--   Inertia: dot Product congr mul Vec star
-- statement:
--   The Inertia construction uses the dot Product congr mul Vec star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L51-L56

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

theorem GlobalTheory.Inertia.dotProduct_congr_mulVec_star (G : Matrix n n ℂ) (P : Matrix n m ℂ) (x y : m → ℂ) :
    x ⬝ᵥ (Pᵀ * G * P.map conj) *ᵥ star y = (P *ᵥ x) ⬝ᵥ G *ᵥ star (P *ᵥ y) := by sorry
