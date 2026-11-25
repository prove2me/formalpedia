-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreCpt_fibre_masses
-- name    : GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:46.713906+00:00
-- url     : https://prove2.me/theorems/10bd0da3-6e41-4866-add7-a84a5afaebbc
-- title:
--   Fibre Cpt: fibre masses
-- statement:
--   The Fibre Cpt construction uses the fibre masses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalBinaryGramIntegral.lean#L150-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalBinaryGramIntegral.lean#L150-L160

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreCpt
open GlobalTheory.CompanionTheory.SW.FibreRatio
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by sorry
