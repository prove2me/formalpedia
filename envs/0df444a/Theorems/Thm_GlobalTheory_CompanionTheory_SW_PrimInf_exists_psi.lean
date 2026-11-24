-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_psi
-- name    : GlobalTheory.CompanionTheory.SW.PrimInf.exists_psi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:40.610228+00:00
-- url     : https://prove2.me/theorems/893494c4-7339-41e1-ba03-5e322f11071c
-- title:
--   Prim Inf: exists psi
-- statement:
--   The Prim Inf construction uses the exists psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L159-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L159-L205

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.PrimInf.exists_psi (ρ : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ) (hρc : ∀ w, Continuous (ρ w))
    (hρs : ∀ w, Continuous (ρ w).symm) (t : InfinitePlace F → ℂ) (htre : ∀ w, (t w).re = 0)
    (htim : ∀ w, (t w).im ≠ 0) :
    ∃ Ψ : (Fin 2 → Ainf F) ≃ₜ (InfinitePlace F → ℂ),
      ∀ p w, Ψ p w = ((ρ w (p 0 w) : ℝ) : ℂ) + ((ρ w (p 1 w) : ℝ) : ℂ) * t w := by sorry
