-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_rational_countable_discrete
-- name    : GlobalTheory.CompanionTheory.SW.rational_countable_discrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:54.032295+00:00
-- url     : https://prove2.me/theorems/4530f22c-5f68-41b3-b482-9b3d6cef079e
-- title:
--   SW: rational countable discrete
-- statement:
--   The SW construction uses the rational countable discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArithmeticUnitaryGroupDiscrete.lean#L9-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArithmeticUnitaryGroupDiscrete.lean#L9-L89

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsNhdsZeroPrincipalEqZero
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArithmeticUnitaryGroupDiscrete
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.rational_countable_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by sorry
