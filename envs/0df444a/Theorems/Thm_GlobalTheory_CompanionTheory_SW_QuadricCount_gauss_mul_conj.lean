-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_gauss_mul_conj
-- name    : GlobalTheory.CompanionTheory.SW.QuadricCount.gauss_mul_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:36.24442+00:00
-- url     : https://prove2.me/theorems/5b9d42d0-5c19-4369-b762-f7b812dbc1f5
-- title:
--   Quadric Count: gauss mul conj
-- statement:
--   The Quadric Count construction uses the gauss mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L42-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteFieldQuadraticFormPointCount.lean#L42-L72

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

theorem GlobalTheory.CompanionTheory.SW.QuadricCount.gauss_mul_conj (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h2 : (2 : k) ≠ 0) {B : Matrix ι ι k}
    (hB : B.IsSymm) (hdet : B.det ≠ 0) {t : k} (ht : t ≠ 0) :
    (∑ x, ψ (t * quadForm B x)) * conj (∑ x, ψ (t * quadForm B x)) =
      (Fintype.card k : ℂ) ^ Fintype.card ι := by sorry
