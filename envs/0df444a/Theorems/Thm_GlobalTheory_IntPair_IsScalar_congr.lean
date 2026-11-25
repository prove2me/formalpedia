-- Prove2me | Theorems.Thm_GlobalTheory_IntPair_IsScalar_congr
-- name    : GlobalTheory.IntPair.IsScalar.congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:33.30042+00:00
-- url     : https://prove2.me/theorems/4700f182-8ad7-5ad7-8e80-43f98e0809ee
-- title:
--   Is Scalar: congr
-- statement:
--   The Is Scalar construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameRedEquivalence.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/SameRedEquivalence.lean#L88-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FinrankLeFinrankInfPerpXPlus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_SameRedEquivalence
import Theorems.Thm_GlobalTheory_SA_IsComp_congr
import Theorems.Thm_GlobalTheory_SA_IsPairMap_congr
import Theorems.Thm_GlobalTheory_SA_IsSig_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IntPair
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Module
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
variable {F F' F'' F₁ G' G'' : FlagD H r} {Λ Λ₁ : Submodule R V} {g : R} {β β₁ s s₁ s₂ : V ≃ₗ[K] V}
variable [FiniteDimensional K V]
omit [FiniteDimensional K V]

theorem GlobalTheory.IntPair.IsScalar.congr (h : IsScalar F F' F'' β) (e : SameRed F' F'' β β₁) : IsScalar F F' F'' β₁ := by sorry
