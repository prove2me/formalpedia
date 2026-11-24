-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_exists_integralBasis_infinitePlace
-- name    : GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:11:30.636566+00:00
-- url     : https://prove2.me/theorems/272afa29-0a21-4317-8333-90e143f8858d
-- title:
--   Th W: exists integral Basis infinite Place
-- statement:
--   The Th W construction uses the exists integral Basis infinite Place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealIntegralBasisExists.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealIntegralBasisExists.lean#L8-L18

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealIntegralBasisExists
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW

theorem GlobalTheory.CompanionTheory.SW.ThW.exists_integralBasis_infinitePlace (F : Type) [Field F] [NumberField F]
    (hF : IsTotallyReal F) : Nonempty (Module.Basis (InfinitePlace F) ℤ (𝓞 F)) := by sorry
