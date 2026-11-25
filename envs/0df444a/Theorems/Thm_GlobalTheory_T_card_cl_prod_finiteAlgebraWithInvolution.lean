-- Prove2me | Theorems.Thm_GlobalTheory_T_card_cl_prod_finiteAlgebraWithInvolution
-- name    : GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:01.641556+00:00
-- url     : https://prove2.me/theorems/0b1dc4bd-300b-47ec-9bd4-a2d60aa8ee4f
-- title:
--   T: card cl prod finite Algebra With Involution
-- statement:
--   The T construction uses the card cl prod finite Algebra With Involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardClProdFiniteAlgebraWithInvolutionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardClProdFiniteAlgebraWithInvolutionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_cl_prod_finiteAlgebraWithInvolution : ∀ (K : UQ) (B₁ B₂ : InvAlg K), Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by sorry
