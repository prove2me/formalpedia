-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_cos_eq_of_rep
-- name    : GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_eq_of_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:44.498203+00:00
-- url     : https://prove2.me/theorems/05fee073-61df-4f32-b4e0-79d32601ded2
-- title:
--   Unitary Conv: cos eq of rep
-- statement:
--   The Unitary Conv construction uses the cos eq of rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L24-L27

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

theorem GlobalTheory.CompanionTheory.RgEis.UnitaryConv.cos_eq_of_rep {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by sorry
