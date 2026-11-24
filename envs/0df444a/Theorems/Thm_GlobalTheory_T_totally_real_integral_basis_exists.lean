-- Prove2me | Theorems.Thm_GlobalTheory_T_totally_real_integral_basis_exists
-- name    : GlobalTheory.T.totally_real_integral_basis_exists
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:51.802713+00:00
-- url     : https://prove2.me/theorems/ee54c1e5-863b-40e3-865f-0cdfe039faea
-- title:
--   T: totally real integral basis exists
-- statement:
--   The T construction uses the totally real integral basis exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealIntegralBasisExistsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealIntegralBasisExistsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealIntegralBasisExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealIntegralBasisExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.totally_real_integral_basis_exists : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by sorry
