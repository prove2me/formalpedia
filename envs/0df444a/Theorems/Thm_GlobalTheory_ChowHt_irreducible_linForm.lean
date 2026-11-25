-- Prove2me | Theorems.Thm_GlobalTheory_ChowHt_irreducible_linForm
-- name    : GlobalTheory.ChowHt.irreducible_linForm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:40.990857+00:00
-- url     : https://prove2.me/theorems/8491c5d1-d4da-40dc-ae07-3d155d7faa23
-- title:
--   Chow Ht: irreducible lin Form
-- statement:
--   The Chow Ht construction uses the irreducible lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallAevalLineVanishingIdealIff.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallAevalLineVanishingIdealIff.lean#L45-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open MvPolynomial NumberField
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.ChowHt.irreducible_linForm {K : Type} [Field K] {N : ℕ} {c : Fin N → K}
    (hc : c ≠ 0) :
    Irreducible (_root_.GlobalTheory.ChowHt.Model.linForm c) := by sorry
