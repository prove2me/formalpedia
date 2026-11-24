-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_unitaryIsom_of_isometry
-- name    : GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:32.587564+00:00
-- url     : https://prove2.me/theorems/bb768bc1-2a61-4ab9-8eea-7aeba543e7b5
-- title:
--   HIsom: unitary Isom of isometry
-- statement:
--   The HIsom construction uses the unitary Isom of isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L96-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L96-L126

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
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
open GlobalTheory.CompanionTheory.SW.HIsom

theorem GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R], ∃ e : HA R σ J' ≃ₜ* HA R σ J, (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J' u * (bc (inclR R) g)⁻¹) ∧ ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J' u ∈ HFin R σ J' := by sorry
