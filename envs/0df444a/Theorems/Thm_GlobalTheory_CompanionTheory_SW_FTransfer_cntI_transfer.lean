-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FTransfer_cntI_transfer
-- name    : GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:43.478287+00:00
-- url     : https://prove2.me/theorems/a1821849-e35d-45fa-aa7b-bc86cd6fb8e3
-- title:
--   FTransfer: cnt I transfer
-- statement:
--   The FTransfer construction uses the cnt I transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L48-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FundamentalDomainTransportCongruentForm.lean#L48-L145

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainTransportCongruentForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory.CompanionTheory.SW.FTransfer

theorem GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by sorry
