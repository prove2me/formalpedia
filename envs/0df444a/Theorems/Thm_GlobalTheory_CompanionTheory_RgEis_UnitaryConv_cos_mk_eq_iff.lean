-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_mk_eq_iff
-- name    : GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:01.023278+00:00
-- url     : https://prove2.me/theorems/346bc533-2808-42ab-a784-b086222fc3b5
-- title:
--   Unitary Conv: cos mk eq iff
-- statement:
--   The Unitary Conv construction uses the cos mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L11-L22

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_mk_eq_iff {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by sorry
