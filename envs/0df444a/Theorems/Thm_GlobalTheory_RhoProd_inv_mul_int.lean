-- Prove2me | Theorems.Thm_GlobalTheory_RhoProd_inv_mul_int
-- name    : GlobalTheory.RhoProd.inv_mul_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:50.665877+00:00
-- url     : https://prove2.me/theorems/21120e60-cc45-4a80-bea7-6a0dcc63764b
-- title:
--   Rho Prod: inv mul int
-- statement:
--   The Rho Prod construction uses the inv mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolution.lean#L58-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolution.lean#L58-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.RhoProd
variable {K : UQ}

theorem GlobalTheory.RhoProd.inv_mul_int (B : InvAlg K) (w : B.A) (g h : B.T)
    (hh : h ∈ (intUnits K.O B.A).subgroupOf B.T) :
    IsIntegral K.O ((((g * h : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) ↔
      IsIntegral K.O ((((g : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A) := by sorry
