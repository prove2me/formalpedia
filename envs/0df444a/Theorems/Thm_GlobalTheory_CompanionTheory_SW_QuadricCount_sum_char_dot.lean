-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_sum_char_dot
-- name    : GlobalTheory.CompanionTheory.SW.QuadricCount.sum_char_dot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:38.430502+00:00
-- url     : https://prove2.me/theorems/3465e3a7-a32e-4991-98aa-ae852a0651e4
-- title:
--   Quadric Count: sum char dot
-- statement:
--   The Quadric Count construction uses the sum char dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L25-L40

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.QuadricCount.sum_char_dot (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {w : ι → k} (hw : w ≠ 0) :
    ∑ y : ι → k, ψ (y ⬝ᵥ w) = 0 := by sorry
