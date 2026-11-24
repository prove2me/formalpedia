-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockForm_blockForms_isHermND
-- name    : GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:19.281516+00:00
-- url     : https://prove2.me/theorems/b602ea48-d209-43ff-903d-f3adf9b60ab0
-- title:
--   Block Form: block Forms is Herm ND
-- statement:
--   The Block Form construction uses the block Forms is Herm ND property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L114-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HyperbolicAndBlockOneNondegenerate.lean#L114-L118

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HyperbolicAndBlockOneNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧
      ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by sorry
