-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_stab_first
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.stab_first
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:09.790601+00:00
-- url     : https://prove2.me/theorems/73b10bce-bf2c-471a-8d78-37006029b886
-- title:
--   Stab First: stab first
-- statement:
--   The Stab First construction uses the stab first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L349-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L349-L362

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst

theorem GlobalTheory.CompanionTheory.SW.StabFirst.stab_first :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R], ∃ ι : HA R σ J →* HA R σ (blockOne (algebraMap F E t) J), IsClosedEmbedding ι ∧ (∀ u, (HA.mat R σ _ (ι u) : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) = blockOne 1 (HA.mat R σ J u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) ∧ (∀ h, h ∈ ι.range ↔ actW R σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) ∧ (∀ u, HA.mat R σ _ (ι u) ∈ HFin R σ (blockOne (algebraMap F E t) J) ↔ HA.mat R σ J u ∈ HFin R σ J) ∧ ∀ (u : HA R σ J) (n : ℕ) (X : Fin n → Fin M → R ⊗[F] E), actW R σ _ (ι u) (consTup X) = consTup (actW R σ J u X) := by sorry
