-- Prove2me | Theorems.Thm_GlobalTheory_T_rho_prod_finiteAlgebraWithInvolution
-- name    : GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:13.728336+00:00
-- url     : https://prove2.me/theorems/b1ad6c50-2031-5675-86ff-435428d08dce
-- title:
--   T: rho prod finite Algebra With Involution
-- statement:
--   The T construction uses the rho prod finite Algebra With Involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolutionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RhoProdFiniteAlgebraWithInvolutionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RhoProdFiniteAlgebraWithInvolutionStatement
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

theorem GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (w₁ : B₁.A) (w₂ : B₂.A), (B₁.prod B₂).rho ((w₁, w₂) : B₁.A × B₂.A) = B₁.rho w₁ * B₂.rho w₂ := by sorry
