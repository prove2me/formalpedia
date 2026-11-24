-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_exists_scale
-- name    : GlobalTheory.CompanionTheory.SW.Core.RowCompletion.exists_scale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:32.259154+00:00
-- url     : https://prove2.me/theorems/0a286555-8391-4c83-bcdb-78e35da9ac80
-- title:
--   Row Completion: exists scale
-- statement:
--   The Row Completion construction uses the exists scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L93-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L93-L150

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.RowCompletion
open nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.Core.RowCompletion.exists_scale (J I : (Ideal (𝓞 F))⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J)
    {c d : 𝓞 F} (hI : (I : Ideal (𝓞 F)) = Ideal.span {c, d}) :
    ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ∧
      ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton _ (l * (c : F)) +
          FractionalIdeal.spanSingleton _ (l * (d : F)) := by sorry
