-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_measure_nonunits_null
-- name    : GlobalTheory.T.haar_measure_nonunits_null
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:43:02.245627+00:00
-- url     : https://prove2.me/theorems/1899a619-de1c-4feb-a5b7-2c1ef09a3136
-- title:
--   T: haar measure nonunits null
-- statement:
--   The T construction uses the haar measure nonunits null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureNonunitsNull.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureNonunitsNull.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureNonunitsNull
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_measure_nonunits_null : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) X)} = 0 := by sorry
