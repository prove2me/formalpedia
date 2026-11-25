-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_Glue_encard_gluings_le
-- name    : GlobalTheory.DegCnt.Glue.encard_gluings_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:21:40.623809+00:00
-- url     : https://prove2.me/theorems/7bfcebe0-c1dd-5ed0-ab1a-d351b5149557
-- title:
--   Glue: encard gluings le
-- statement:
--   The Glue construction uses the encard gluings le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUnimodularHermGluingsLe.lean#L176-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardUnimodularHermGluingsLe.lean#L176-L260

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUnimodularHermGluingsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Glue
open TensorProduct
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.Glue.encard_gluings_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (U : Submodule K V) (A B : Submodule (𝓞 K) V) (x : ℕ), IsCompl U (perp H U) → idx (dual H A) A = x → ((({Λ : Submodule (𝓞 K) V | IsUnimod H Λ ∧ Λ ⊓ rs (𝓞 K) U = A ∧ Λ ⊓ rs (𝓞 K) (perp H U) = B}).encard : ℕ∞) : ℝ≥0∞) ≤ (x : ℝ≥0∞) ^ Module.finrank K (perp H U) := by sorry
