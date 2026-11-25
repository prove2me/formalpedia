-- Prove2me | Theorems.Thm_GlobalTheory_SA_FlagExample_exists_pair
-- name    : GlobalTheory.SA.FlagExample.exists_pair
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:19.218899+00:00
-- url     : https://prove2.me/theorems/a2dee30a-c5de-46fc-a0fd-70624a3e4ecf
-- title:
--   Flag Example: exists pair
-- statement:
--   The Flag Example construction uses the exists pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L647-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/SymmetricFlagBasisVectorsApplyCentre.lean#L647-L659

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
open GlobalTheory.SA.FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)

theorem GlobalTheory.SA.FlagExample.exists_pair : ∃ (F F' F'' : FlagD (ofHSpace (wittSpace E 2 1)) 1)
    (β : (wittSpace E 2 1).V ≃ₗ[E] (wittSpace E 2 1).V),
    IsUnimod (ofHSpace (wittSpace E 2 1)) (wittSpace E 2 1).L0 ∧
    F.z ∈ (wittSpace E 2 1).L0 ∧ F'.z ∈ (wittSpace E 2 1).L0 ∧ F''.z ∈ (wittSpace E 2 1).L0 ∧
    F.T = 1 ∧ F'.T = 1 ∧ F''.T = 1 ∧
    IsCong F F' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧ IsCong F F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧
    Gval F F' ≠ 0 ∧ Gval F F'' ≠ 0 ∧ IsTransv F F' ∧ IsTransv F F'' ∧ F'.X ≠ F''.X ∧
    IsPairMap F F' F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) β := by sorry
