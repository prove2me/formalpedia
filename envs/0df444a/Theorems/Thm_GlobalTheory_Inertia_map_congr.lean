-- Prove2me | Theorems.Thm_GlobalTheory_Inertia_map_congr
-- name    : GlobalTheory.Inertia.map_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:14.862856+00:00
-- url     : https://prove2.me/theorems/d0edd35b-8516-4f50-9435-bdc3e1078723
-- title:
--   Inertia: map congr
-- statement:
--   The Inertia construction uses the map congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L476-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/PosIndexMapEqCardOfCongrDiagonal.lean#L476-L481

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
omit [DecidableEq n]

theorem GlobalTheory.Inertia.map_congr {m : Type*} (τ : E →+* ℂ) (G : Matrix n n E) (P : Matrix n m E) :
    (Pᵀ * G * P.map FD.cc).map τ = (P.map τ)ᵀ * G.map τ * (P.map τ).map conj := by sorry
