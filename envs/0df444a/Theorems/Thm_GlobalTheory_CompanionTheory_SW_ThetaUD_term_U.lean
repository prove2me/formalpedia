-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_term_U
-- name    : GlobalTheory.CompanionTheory.SW.ThetaUD.term_U
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:27.505903+00:00
-- url     : https://prove2.me/theorems/eb34d850-3bd8-4057-8ed8-bf960c4febc9
-- title:
--   Theta UD: term U
-- statement:
--   The Theta UD construction uses the term U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L76-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L76-L116

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.ThetaUD.term_U (ψ : AddChar (A F) ℂ) (hψ : IsStdChar F ψ) (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (hQ : QSetup M B ρ P)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (hO : IsOrth B ρ gf gi)
    (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ) (b : F) (x : ι → F) :
    thTerm B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) x =
      thTerm B ρ P gf gi φ τ x := by sorry
