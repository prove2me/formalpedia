-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_ClProd_card_cl_prod
-- name    : GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:18.943159+00:00
-- url     : https://prove2.me/theorems/588ab8e6-98db-444f-910b-393cda7c81cf
-- title:
--   Cl Prod: card cl prod
-- statement:
--   The Cl Prod construction uses the card cl prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardClProdFiniteAlgebraWithInvolution.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardClProdFiniteAlgebraWithInvolution.lean#L55-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardClProdFiniteAlgebraWithInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.InvAlg GlobalTheory.UnitLemma.InvAlg.ClProd
variable {K : UQ} (B₁ B₂ : InvAlg K)

theorem GlobalTheory.UnitLemma.InvAlg.ClProd.card_cl_prod (K : UQ) (B₁ B₂ : InvAlg K) :
    Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by sorry
