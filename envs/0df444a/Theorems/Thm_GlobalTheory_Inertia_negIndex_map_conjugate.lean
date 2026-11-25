-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_negIndex_map_conjugate
-- name    : GlobalTheory.Inertia.negIndex_map_conjugate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:03.771226+00:00
-- url     : https://prove2.me/theorems/32d4e822-3d94-5cf5-83f9-da0c40760d9e
-- title:
--   Inertia: neg Index map conjugate
-- statement:
--   The Inertia construction uses the neg Index map conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L469-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L469-L472

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
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.Inertia.negIndex_map_conjugate (τ : E →+* ℂ) {G : Matrix n n E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    negIndex (G.map (ComplexEmbedding.conjugate τ)) = negIndex (G.map τ) := by sorry
