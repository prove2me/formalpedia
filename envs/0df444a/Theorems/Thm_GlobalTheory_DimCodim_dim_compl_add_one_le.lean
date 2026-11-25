-- Prove2me | Theorems.Thm_GlobalTheory_DimCodim_dim_compl_add_one_le
-- name    : GlobalTheory.DimCodim.dim_compl_add_one_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:50.133209+00:00
-- url     : https://prove2.me/theorems/50942a59-b37f-5f9d-85eb-e58487490cf9
-- title:
--   Dim Codim: dim compl add one le
-- statement:
--   The Dim Codim construction uses the dim compl add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedComplementDimBound.lean#L37-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClosedComplementDimBound.lean#L37-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosedComplementDimBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.DimCodim

theorem GlobalTheory.DimCodim.dim_compl_add_one_le (X : Scheme.{0}) (U : X.Opens) (d : ℕ)
    (hX : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hU : ∀ y : X, ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U) :
    topologicalKrullDim ((U : Set X)ᶜ : Set X) + 1 ≤ (d : WithBot ℕ∞) := by sorry
